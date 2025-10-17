`define ddtp_iommu_mode riscv_iommu.ddtp.iommu_mode.q
`define ddtp_busy riscv_iommu.ddtp.busy.q

`define ar_valid dev_tr_req_i.ar_valid
`define ar_ready dev_tr_resp_o.ar_ready

`define aw_valid dev_tr_req_i.aw_valid
`define aw_ready dev_tr_resp_o.aw_ready

// -------------------Cutpoint Assumptions Started------------------
// debug mode is not supported so this is tied to 0
assmp1_debug_0:
assume property (riscv_iommu.dbg_if_ctl==0);

// 5-15 are reserved bits
assmp2_ddtp_write:
assume property (`ddtp_iommu_mode < 5);

assmp3_ddtp_stable_for_ar_channel:
assume property (`ar_valid && (`ar_ready==0) |=> $stable(riscv_iommu.ddtp.iommu_mode.q));

assmp4_ddtp_stable_for_aw_channel:
assume property (`aw_valid && (`aw_ready==0) |=> $stable(riscv_iommu.ddtp.iommu_mode.q));

assmp5_little_endian_access_only:
assume property(riscv_iommu.fctl.be==0);

assmp6_enable_wiredsignal_interrupts:
assume property(riscv_iommu.fctl.wsi==1);
// -------------------Cutpoint Assumptions Ended--------------------

// -------------------Overconstraint Assumptions Started-------------
// AXI transaction lengths are constrained to less than 5
oc1_length_small:
assume property (dev_tr_req_i.aw.len < 5 && dev_tr_req_i.ar.len < 5);

// Guest translation scheme isn't supported in current TB
oc2_fctl_to_zero:
assume property(riscv_iommu.fctl.gxl==0);

// Flushing of cache isn't supported in current TB
oc3_zero_flush:
assume property ((riscv_iommu.flush_ddtc==0) && (riscv_iommu.flush_pdtc==0) && (riscv_iommu.flush_vma==0) && (riscv_iommu.flush_vma==0) && (riscv_iommu.flush_gvma==0));
// -------------------Overconstraint Assumptions Ended-------------
