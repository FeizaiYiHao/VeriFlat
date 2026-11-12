//! BAR0 register offsets and fields used by the driver (E810 datasheet: register descriptions; the values match the
//! Linux `ice_hw_autogen.h`). Queue-indexed registers take the PF's own queue index (0 = the PF's first queue), as
//! the Linux driver passes them.

/// Global reset status; `DEVSTATE` is 0 when no global reset is in progress.
pub const GLGEN_RSTAT: usize = 0x000B_8188;
pub const GLGEN_RSTAT_DEVSTATE_M: u32 = 0x3;
/// NVM "unit load done" bits; all of `GLNVM_ULD_RESET_DONE` are set once the device left its last reset.
pub const GLNVM_ULD: usize = 0x000B_6008;
/// PCIER_DONE (0), PCIER_DONE_1 (1), CORER_DONE (3), GLOBR_DONE (4), POR_DONE (5), POR_DONE_1 (8), PCIER_DONE_2 (9).
pub const GLNVM_ULD_RESET_DONE: u32 = (1 << 0) | (1 << 1) | (1 << 3) | (1 << 4) | (1 << 5) | (1 << 8) | (1 << 9);
/// PF control; writing `PFSWR` starts a PF software reset, which clears the bit when it is done.
pub const PFGEN_CTRL: usize = 0x0009_1000;
pub const PFGEN_CTRL_PFSWR: u32 = 1 << 0;
/// The PCI function number of this PF in bits 2:0.
pub const PF_FUNC_RID: usize = 0x0009_E880;
pub const PF_FUNC_RID_FUNC_NUM_M: u32 = 0x7;

/// Admin transmit queue (driver to firmware) and admin receive queue (firmware events).
pub const PF_FW_ATQBAL: usize = 0x0008_0000;
pub const PF_FW_ARQBAL: usize = 0x0008_0080;
pub const PF_FW_ATQBAH: usize = 0x0008_0100;
pub const PF_FW_ARQBAH: usize = 0x0008_0180;
pub const PF_FW_ATQLEN: usize = 0x0008_0200;
pub const PF_FW_ARQLEN: usize = 0x0008_0280;
pub const PF_FW_ATQH: usize = 0x0008_0300;
pub const PF_FW_ARQH: usize = 0x0008_0380;
pub const PF_FW_ATQT: usize = 0x0008_0400;
pub const PF_FW_ARQT: usize = 0x0008_0480;
/// Length field and status bits of `PF_FW_ATQLEN`/`PF_FW_ARQLEN`, and the head/tail index field.
pub const PF_FW_QLEN_M: u32 = 0x3FF;
pub const PF_FW_QLEN_VFE: u32 = 1 << 28;
pub const PF_FW_QLEN_OVFL: u32 = 1 << 29;
pub const PF_FW_QLEN_CRIT: u32 = 1 << 30;
pub const PF_FW_QLEN_ENABLE: u32 = 1 << 31;
pub const PF_FW_QH_M: u32 = 0x3FF;

/// "Other" interrupt cause enables; the driver keeps them 0.
pub const PFINT_OICR_ENA: usize = 0x0016_C900;

/// Rx queue context dword `i` (0..8) of PF queue `q`.
pub const fn qrx_context(i: usize, q: usize) -> usize {
    0x0028_0000 + i * 8192 + q * 4
}
/// Rx queue enable request and status.
pub const fn qrx_ctrl(q: usize) -> usize {
    0x0012_0000 + q * 4
}
pub const QRX_CTRL_QENA_REQ: u32 = 1 << 0;
pub const QRX_CTRL_QENA_STAT: u32 = 1 << 2;
/// Rx tail: the first descriptor the device must not use.
pub const fn qrx_tail(q: usize) -> usize {
    0x0029_0000 + q * 4
}
/// Rx descriptor format (RXDID) and its priority.
pub const fn qrxflxp_cntxt(q: usize) -> usize {
    0x0048_0000 + q * 4
}
pub const QRXFLXP_CNTXT_RXDID_IDX_M: u32 = 0x3F;
pub const QRXFLXP_CNTXT_RXDID_PRIO_S: u32 = 8;
pub const QRXFLXP_CNTXT_RXDID_PRIO_M: u32 = 0x7 << 8;
pub const QRXFLXP_CNTXT_TS: u32 = 1 << 11;
/// Tx doorbell (tail) of PF queue `q`.
pub const fn qtx_comm_dbell(q: usize) -> usize {
    0x002C_0000 + q * 4
}

/// Port statistics of logical port `p`: 40-bit counters as a low register and a high register 4 bytes above it
/// whose bits 7:0 hold counter bits 39:32.
pub const fn glprt_gorcl(p: usize) -> usize {
    0x0038_0000 + p * 8
}
pub const fn glprt_gotcl(p: usize) -> usize {
    0x0038_0B40 + p * 8
}
pub const fn glprt_uprcl(p: usize) -> usize {
    0x0038_1300 + p * 8
}
pub const fn glprt_mprcl(p: usize) -> usize {
    0x0038_1340 + p * 8
}
pub const fn glprt_bprcl(p: usize) -> usize {
    0x0038_1380 + p * 8
}
pub const fn glprt_uptcl(p: usize) -> usize {
    0x0038_11C0 + p * 8
}
pub const fn glprt_mptcl(p: usize) -> usize {
    0x0038_1200 + p * 8
}
pub const fn glprt_bptcl(p: usize) -> usize {
    0x0038_1240 + p * 8
}
/// CRC errors and illegal bytes, 32-bit counters.
pub const fn glprt_crcerrs(p: usize) -> usize {
    0x0038_0100 + p * 8
}
pub const fn glprt_illerrc(p: usize) -> usize {
    0x0038_01C0 + p * 8
}
