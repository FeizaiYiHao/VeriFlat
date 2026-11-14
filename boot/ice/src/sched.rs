//! The Tx scheduler tree (E810 datasheet: transmit scheduler, and the Tx scheduler admin commands). The
//! firmware builds a default tree per port, root (layer 0) and traffic class (layer 1) nodes and a chain of nodes down
//! to a leaf; every Tx queue must hang under a node of the queue group layer (two above the last layer). The driver
//! does what the Linux driver does for one VSI: it removes the firmware's default nodes from the "entry point" layer
//! down, adds one node per layer below the remaining chain down to the layer above the queue groups, then enough
//! queue group nodes for its queues.

use alloc::vec::Vec;

/// Element types.
pub const ELEM_TYPE_ROOT_PORT: u8 = 0x1;
pub const ELEM_TYPE_TC: u8 = 0x2;
pub const ELEM_TYPE_SE_GENERIC: u8 = 0x3;
pub const ELEM_TYPE_ENTRY_POINT: u8 = 0x4;
pub const ELEM_TYPE_LEAF: u8 = 0x5;
/// Valid sections of an element: generic, committed rate, excess rate.
pub const ELEM_VALID_GENERIC: u8 = 1 << 0;
pub const ELEM_VALID_CIR: u8 = 1 << 1;
pub const ELEM_VALID_EIR: u8 = 1 << 2;
/// Default rate limit profile and bandwidth weight of a new element.
pub const DFLT_RL_PROF_ID: u16 = 0;
pub const DFLT_BW_WT: u16 = 4;
/// Most layers of a tree.
pub const MAX_LAYERS: usize = 9;

/// A 16-byte element description (`ice_aqc_txsched_elem`): type, valid sections, generic, flags, CIR and EIR
/// (profile, weight), shared rate limit ID.
pub const ELEM_INFO_BYTES: usize = 16;
/// An element with its parent and own TEID (`ice_aqc_txsched_elem_data`).
pub const ELEM_DATA_BYTES: usize = 24;
/// A group header (`ice_aqc_txsched_topo_grp_info_hdr`): parent TEID, element count.
pub const GRP_HDR_BYTES: usize = 8;
/// One branch of the default topology: a header and up to 9 elements.
pub const TOPO_BRANCH_BYTES: usize = GRP_HDR_BYTES + MAX_LAYERS * ELEM_DATA_BYTES;
/// Query Scheduler Resource Allocation response: 32 bytes of generic properties, then 32 bytes per layer.
pub const RES_GENERIC_BYTES: usize = 32;
pub const RES_LAYER_BYTES: usize = 32;
/// `max_sibl_grp_sz` in a layer's properties (after layer, chunk size, two node counts and 4 reserved bytes).
pub const LAYER_MAX_SIBL: usize = 10;
pub const RES_BUF_BYTES: usize = RES_GENERIC_BYTES + MAX_LAYERS * RES_LAYER_BYTES;

fn le16(b: &[u8], o: usize) -> u16 {
    u16::from_le_bytes([b[o], b[o + 1]])
}

fn le32(b: &[u8], o: usize) -> u32 {
    u32::from_le_bytes([b[o], b[o + 1], b[o + 2], b[o + 3]])
}

/// The 16-byte description of a new generic node or queue with the default rate limits, as the Linux driver fills it.
pub fn default_elem_info(elem_type: u8) -> [u8; ELEM_INFO_BYTES] {
    let mut e = [0u8; ELEM_INFO_BYTES];
    e[0] = elem_type;
    e[1] = ELEM_VALID_GENERIC | ELEM_VALID_CIR | ELEM_VALID_EIR;
    e[2] = 0;
    e[4..6].copy_from_slice(&DFLT_RL_PROF_ID.to_le_bytes());
    e[6..8].copy_from_slice(&DFLT_BW_WT.to_le_bytes());
    e[8..10].copy_from_slice(&DFLT_RL_PROF_ID.to_le_bytes());
    e[10..12].copy_from_slice(&DFLT_BW_WT.to_le_bytes());
    e
}

/// What Query Scheduler Resource Allocation said.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SchedResources {
    /// Logical layers of the tree.
    pub layers: usize,
    /// Most children a node of layer `i` may have (`max_sibl_grp_sz` of layer `i + 1`).
    pub max_children: [u16; MAX_LAYERS],
}

impl SchedResources {
    pub fn parse(buf: &[u8]) -> Option<SchedResources> {
        let layers = le16(buf, 2) as usize;
        if layers < 3 || layers > MAX_LAYERS || buf.len() < RES_BUF_BYTES {
            return None;
        }
        let mut max_children = [0u16; MAX_LAYERS];
        for (i, m) in max_children.iter_mut().enumerate().take(layers - 1) {
            *m = le16(buf, RES_GENERIC_BYTES + (i + 1) * RES_LAYER_BYTES + LAYER_MAX_SIBL);
        }
        Some(SchedResources { layers, max_children })
    }

    /// The queue group layer: queues hang under its nodes.
    pub fn qgroup_layer(&self) -> usize {
        self.layers - 2
    }
}

/// A node of the default topology.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Node {
    pub layer: usize,
    pub parent_teid: u32,
    pub teid: u32,
    pub elem_type: u8,
}

/// The branches of Get Default Topology's response, each from the root down.
pub fn parse_topology(buf: &[u8], num_branches: usize) -> Option<Vec<Vec<Node>>> {
    if num_branches == 0 || num_branches * TOPO_BRANCH_BYTES > buf.len() {
        return None;
    }
    let mut branches = Vec::new();
    for b in 0..num_branches {
        let base = b * TOPO_BRANCH_BYTES;
        let n = le16(buf, base + 4) as usize;
        if n == 0 || n > MAX_LAYERS {
            return None;
        }
        let nodes = (0..n)
            .map(|j| {
                let e = base + GRP_HDR_BYTES + j * ELEM_DATA_BYTES;
                Node { layer: j, parent_teid: le32(buf, e), teid: le32(buf, e + 4), elem_type: buf[e + 8] }
            })
            .collect();
        branches.push(nodes);
    }
    Some(branches)
}

/// The software entry point layer: the layer of branch 0's entry point element.
pub fn entry_point_layer(branches: &[Vec<Node>]) -> Option<usize> {
    branches[0].iter().skip(1).find(|n| n.elem_type == ELEM_TYPE_ENTRY_POINT).map(|n| n.layer)
}

/// The default nodes to delete, deepest first: the subtree of branch 0's first node at or below the entry point layer
/// that is neither root nor traffic class, across every branch that shares it.
pub fn default_nodes_to_remove(branches: &[Vec<Node>], entry_layer: usize) -> Vec<Node> {
    let Some(top) = branches[0].iter().find(|n| n.layer >= entry_layer && n.elem_type != ELEM_TYPE_ROOT_PORT && n.elem_type != ELEM_TYPE_TC)
    else {
        return Vec::new();
    };
    let mut doomed: Vec<Node> = Vec::new();
    for branch in branches {
        if let Some(pos) = branch.iter().position(|n| n.teid == top.teid) {
            for n in &branch[pos..] {
                if !doomed.iter().any(|d| d.teid == n.teid) {
                    doomed.push(*n);
                }
            }
        }
    }
    doomed.sort_by(|a, b| b.layer.cmp(&a.layer));
    doomed
}

/// The deepest node of branch 0 that stays after the removal: the parent of the driver's new chain.
pub fn chain_parent(branches: &[Vec<Node>], removed: &[Node]) -> Node {
    *branches[0].iter().rev().find(|n| !removed.iter().any(|r| r.teid == n.teid)).expect("the root stays")
}

/// The driver's plan below `parent`: one generic node per layer down to the layer above the queue groups, then
/// `qgroups` queue group nodes, each taking up to `per_qgroup` queues.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plan {
    pub chain_layers: core::ops::Range<usize>,
    pub qgroups: usize,
    pub per_qgroup: usize,
}

pub fn plan(res: &SchedResources, parent: &Node, queues: usize) -> Result<Plan, &'static str> {
    let qgl = res.qgroup_layer();
    if parent.layer >= qgl {
        return Err("the default topology leaves no room above the queue group layer");
    }
    let per_qgroup = res.max_children[qgl] as usize;
    if per_qgroup == 0 {
        return Err("queue group nodes take no queues");
    }
    let qgroups = queues.div_ceil(per_qgroup);
    let above = if parent.layer + 1 == qgl { parent.layer } else { qgl - 1 };
    if qgroups > res.max_children[above] as usize {
        return Err("more queue groups than one node of the layer above takes");
    }
    Ok(Plan { chain_layers: parent.layer + 1..qgl, qgroups, per_qgroup })
}

/// Canned firmware answers for the tests and the device model.
#[cfg(any(test, feature = "mock"))]
pub(crate) mod canned {
    use super::*;

    /// A default topology of 9 layers as E810 firmware reports it: root, TC, three generic nodes, an entry point at
    /// layer 5, two generic nodes and a leaf. TEIDs are 0x10 + layer.
    pub fn default_topology_buf() -> alloc::vec::Vec<u8> {
        let types = [ELEM_TYPE_ROOT_PORT, ELEM_TYPE_TC, 3, 3, 3, ELEM_TYPE_ENTRY_POINT, 3, 3, ELEM_TYPE_LEAF];
        let mut buf = alloc::vec![0u8; 4096];
        buf[0..4].copy_from_slice(&0xffff_ffffu32.to_le_bytes());
        buf[4..6].copy_from_slice(&9u16.to_le_bytes());
        for (j, &t) in types.iter().enumerate() {
            let e = GRP_HDR_BYTES + j * ELEM_DATA_BYTES;
            let parent = if j == 0 { 0xffff_ffff } else { 0x10 + j as u32 - 1 };
            buf[e..e + 4].copy_from_slice(&parent.to_le_bytes());
            buf[e + 4..e + 8].copy_from_slice(&(0x10 + j as u32).to_le_bytes());
            buf[e + 8] = t;
        }
        buf
    }

    pub fn resources_buf(layers: u16, max_sibl: [u16; MAX_LAYERS]) -> alloc::vec::Vec<u8> {
        let mut buf = alloc::vec![0u8; RES_BUF_BYTES];
        buf[0..2].copy_from_slice(&layers.to_le_bytes());
        buf[2..4].copy_from_slice(&layers.to_le_bytes());
        for (i, m) in max_sibl.iter().enumerate() {
            let o = RES_GENERIC_BYTES + i * RES_LAYER_BYTES;
            buf[o] = i as u8;
            buf[o + LAYER_MAX_SIBL..o + LAYER_MAX_SIBL + 2].copy_from_slice(&m.to_le_bytes());
        }
        buf
    }
}

#[cfg(test)]
mod tests {
    use super::canned::*;
    use super::*;

    #[test]
    fn parse_and_plan() {
        let res = SchedResources::parse(&resources_buf(9, [1, 1, 8, 8, 8, 8, 8, 8, 8])).unwrap();
        assert_eq!(res.layers, 9);
        assert_eq!(res.max_children[0], 1);
        assert_eq!(res.max_children[7], 8);
        assert_eq!(res.max_children[8], 0);
        assert_eq!(res.qgroup_layer(), 7);

        let branches = parse_topology(&default_topology_buf(), 1).unwrap();
        assert_eq!(branches[0].len(), 9);
        assert_eq!(branches[0][1], Node { layer: 1, parent_teid: 0x10, teid: 0x11, elem_type: ELEM_TYPE_TC });
        let entry = entry_point_layer(&branches).unwrap();
        assert_eq!(entry, 5);
        let doomed = default_nodes_to_remove(&branches, entry);
        assert_eq!(doomed.iter().map(|n| n.teid).collect::<Vec<_>>(), [0x18, 0x17, 0x16, 0x15]);
        let parent = chain_parent(&branches, &doomed);
        assert_eq!(parent.teid, 0x14);
        let p = plan(&res, &parent, 28).unwrap();
        assert_eq!(p, Plan { chain_layers: 5..7, qgroups: 4, per_qgroup: 8 });
        assert!(plan(&res, &parent, 65).is_err());
    }

    #[test]
    fn plan_directly_under_parent() {
        let res = SchedResources::parse(&resources_buf(5, [1, 4, 8, 16, 8, 0, 0, 0, 0])).unwrap();
        let parent = Node { layer: 2, parent_teid: 1, teid: 2, elem_type: 3 };
        // qgroup layer 3 sits right under the parent: no chain.
        let p = plan(&res, &parent, 20).unwrap();
        assert_eq!(p, Plan { chain_layers: 3..3, qgroups: 3, per_qgroup: 8 });
    }

    #[test]
    fn elem_info() {
        let e = default_elem_info(ELEM_TYPE_SE_GENERIC);
        assert_eq!(e, [3, 7, 0, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0, 0, 0]);
    }
}
