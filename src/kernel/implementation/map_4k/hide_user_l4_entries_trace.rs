use vstd::prelude::*;
use crate::*;
use super::hide_user_l4_entries_eof::*;

verus! {
/// Hiding user root entry `l4i` of `pagetable` that changes what some table maps changes the user view: the owning process
/// shows the table unless it is a zombie, and a zombie's table maps nothing.
pub proof fn hide_user_l4_entries_hide_step_pre_from_k(pre: &KernelK, post: &KernelK, pagetable: RwLockPageTableRoot, l4i: L4Index)
    requires
        pre.inv(),
        hide_user_l4_entry_eof_transition_framing(*pre, *post, pagetable, l4i),
        !kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view()),
    ensures kernel_k_to_kernel_u(*pre) != kernel_k_to_kernel_u(*post),
{
    reveal(hide_user_l4_entry_eof_transition_framing);
    let prc_ptr = pre.pt_mp.spec_index(pagetable).view().proc_ptr;
    let old_c = whole_pagetable(pre.pt_mp, pre.pt_lower.view(), pagetable);
    let new_c = whole_pagetable(post.pt_mp, post.pt_lower.view(), pagetable);
    pagetable_l4_entry_hidden_implies_u_pagetable_l4_range_removed(*pre, *post, pagetable, l4i);
    process_pagetable_match_pagetable_at(pre.prc_mp, pre.pt_mp, pagetable);
    process_perms_wf_at(pre.prc_mp, prc_ptr);
    process_emptied_tables_wf_at(pre.prc_mp, pre.pt_mp, pre.pt_lower.view(), pre.it_mp, pre.pg_arr, prc_ptr);
    pagetable_no_1g_leaf_wf_at(pre.pt_mp, pre.pt_lower.view(), pagetable);
    kernel_process_projection_at(post, prc_ptr);
    if pre.prc_mp.spec_index(prc_ptr).view().zombie {
        assert(new_c.mapping_4k() =~= old_c.mapping_4k()); assert(new_c.mapping_2m() =~= old_c.mapping_2m()); assert(new_c.mapping_1g() =~= old_c.mapping_1g());
    }
    assert(kernel_k_to_kernel_u(*pre) == kernel_k_to_kernel_u(*post) || pre.prc_mp.spec_index(prc_ptr).view().zombie
        ==> kernel_pagetable_nonlock_fields_unchanged(pre.pt_mp, pre.pt_lower.view(), post.pt_mp, post.pt_lower.view())) by { reveal(kernel_pagetable_nonlock_fields_unchanged); };
}

/// Hiding user root entry `l4i` of `pagetable` from `pre` to `post` drops every 4K, 2M and 1G mapping and every window lock under
/// `l4i` from the table its owning process shows, if any, and keeps the rest of the user view.
pub proof fn hide_user_l4_entries_hide_step_from_k(pre: &KernelK, post: &KernelK, pagetable: RwLockPageTableRoot, l4i: L4Index)
    requires
        process_pagetable_match(pre.prc_mp, pre.pt_mp),
        hide_user_l4_entry_eof_transition_framing(*pre, *post, pagetable, l4i),
    ensures
        ({
            let old_u = kernel_k_to_kernel_u(*pre);
            let prc_ptr = pre.pt_mp.spec_index(pagetable).view().proc_ptr;
            let table = old_u.process_map[prc_ptr].pagetable->Some_0;
            &&& old_u.process_map.dom().contains(prc_ptr)
            &&& kernel_k_to_kernel_u(*post) == (KernelU {
                process_map: old_u.process_map.insert(prc_ptr, ProcessU {
                    pagetable: if old_u.process_map[prc_ptr].pagetable is Some {
                        Some(PageTableU {
                            mapping_4k: table.mapping_4k.remove_keys(table.mapping_4k.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
                            mapping_2m: table.mapping_2m.remove_keys(table.mapping_2m.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
                            mapping_1g: table.mapping_1g.remove_keys(table.mapping_1g.dom().filter(|va: VAddr| spec_v2l4index(va) == l4i)),
                            pagetable_window_locks: table.pagetable_window_locks.remove_keys(table.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == l4i)),
                            ..table
                        })
                    } else {
                        None
                    },
                    ..old_u.process_map[prc_ptr]
                }),
                ..old_u
            })
        }),
{
    reveal(hide_user_l4_entry_eof_transition_framing);
    pagetable_l4_entry_hidden_implies_u_pagetable_l4_range_removed(*pre, *post, pagetable, l4i);
}

/// The steps `steps[start + k]`, each recorded across hiding user root entry `hidden[k].0` of `pagetable` from `hidden[k].1` to
/// `hidden[k].2`, each drop the mappings and window locks under that entry from the table the owning process shows, if any,
/// and keep the rest of the user view.
pub proof fn hide_user_l4_entries_steps_from_k(steps: Seq<KernelStep>, start: int, hidden: Seq<(L4Index, KernelK, KernelK)>, pagetable: RwLockPageTableRoot, count: int)
    requires
        0 <= start,
        0 <= count <= hidden.len(),
        start + hidden.len() <= steps.len(),
        forall|k: int| #![trigger hidden[k]] 0 <= k < hidden.len() ==> {
            &&& steps[start + k] == (KernelStep { old_u: kernel_k_to_kernel_u(hidden[k].1), new_u: kernel_k_to_kernel_u(hidden[k].2) })
            &&& process_pagetable_match(hidden[k].1.prc_mp, hidden[k].1.pt_mp)
            &&& hide_user_l4_entry_eof_transition_framing(hidden[k].1, hidden[k].2, pagetable, hidden[k].0)
        },
    ensures
        forall|k: int| #![trigger hidden[k]] 0 <= k < count ==> {
            let step = steps[start + k];
            let prc_ptr = hidden[k].1.pt_mp.spec_index(pagetable).view().proc_ptr;
            let table = step.old_u.process_map[prc_ptr].pagetable->Some_0;
            &&& step.old_u.process_map.dom().contains(prc_ptr)
            &&& step.new_u == (KernelU {
                process_map: step.old_u.process_map.insert(prc_ptr, ProcessU {
                    pagetable: if step.old_u.process_map[prc_ptr].pagetable is Some {
                        Some(PageTableU {
                            mapping_4k: table.mapping_4k.remove_keys(table.mapping_4k.dom().filter(|va: VAddr| spec_v2l4index(va) == hidden[k].0)),
                            mapping_2m: table.mapping_2m.remove_keys(table.mapping_2m.dom().filter(|va: VAddr| spec_v2l4index(va) == hidden[k].0)),
                            mapping_1g: table.mapping_1g.remove_keys(table.mapping_1g.dom().filter(|va: VAddr| spec_v2l4index(va) == hidden[k].0)),
                            pagetable_window_locks: table.pagetable_window_locks.remove_keys(table.pagetable_window_locks.dom().filter(|w: WindowVa| spec_v2l4index(w.va) == hidden[k].0)),
                            ..table
                        })
                    } else {
                        None
                    },
                    ..step.old_u.process_map[prc_ptr]
                }),
                ..step.old_u
            })
        },
    decreases count,
{
    if count > 0 {
        hide_user_l4_entries_steps_from_k(steps, start, hidden, pagetable, count - 1);
        hide_user_l4_entries_hide_step_from_k(&hidden[count - 1].1, &hidden[count - 1].2, pagetable, hidden[count - 1].0);
    }
}
}
