module iommu_sva #(
    // Number of IOTLB entries
    parameter int unsigned  IOTLB_ENTRIES       = 4,
    // Number of DDTC entries
    parameter int unsigned  DDTC_ENTRIES        = 4,
    // Number of PDTC entries
    parameter int unsigned  PDTC_ENTRIES        = 4,
    // Number of MRIF cache entries (if supported)
    parameter int unsigned  MRIFC_ENTRIES       = 4,

    // Include process_id support
    parameter bit                   InclPC      = 0,
    // Include AXI4 address boundary check
    parameter bit                   InclBC      = 0,
    // Include debug register interface
    parameter bit                   InclDBG     = 0,

    // MSI translation support
    parameter rv_iommu::msi_trans_t MSITrans    = rv_iommu::MSI_DISABLED,
    // Interrupt Generation Support
    parameter rv_iommu::igs_t       IGS         = rv_iommu::WSI_ONLY,
    // Number of interrupt vectors supported
    parameter int unsigned      N_INT_VEC       = 16,
    // Number of Performance monitoring event counters (set to zero to disable HPM)
    parameter int unsigned      N_IOHPMCTR      = 0,     // max 31

    /// AXI Bus Addr width.
    parameter int   ADDR_WIDTH      = -1,
    /// AXI Bus data width.
    parameter int   DATA_WIDTH      = -1,
    /// AXI ID width
    parameter int   ID_WIDTH        = -1,
    /// AXI ID width
    parameter int   ID_SLV_WIDTH    = -1,
    /// AXI user width
    parameter int   USER_WIDTH      = 1,
    /// AXI AW Channel struct type
    parameter type aw_chan_t        = logic,
    /// AXI W Channel struct type
    parameter type w_chan_t         = logic,
    /// AXI B Channel struct type
    parameter type b_chan_t         = logic,
    /// AXI AR Channel struct type
    parameter type ar_chan_t        = logic,
    /// AXI R Channel struct type
    parameter type r_chan_t         = logic,
    /// AXI Full request struct type
    parameter type  axi_req_t       = logic,
    /// AXI Full response struct type
    parameter type  axi_rsp_t       = logic,
    /// AXI Full Slave request struct type
    parameter type  axi_req_slv_t   = logic,
    /// AXI Full Slave response struct type
    parameter type  axi_rsp_slv_t   = logic,
    /// AXI Full request struct type w/ DVM extension for SMMU
    parameter type  axi_req_iommu_t = logic,
    /// Regbus request struct type.
    parameter type  reg_req_t       = logic,
    /// Regbus response struct type.
    parameter type  reg_rsp_t       = logic
) (
    input  logic clk_i,
    input  logic rst_ni,

    // Translation Request Interface (Slave)
    input  axi_req_iommu_t  dev_tr_req_i,
    input  axi_rsp_t        dev_tr_resp_o,

    // Translation Completion Interface (Master)
    input  axi_rsp_t        dev_comp_resp_i,
    input  axi_req_t        dev_comp_req_o,

    // Data Structures Interface (Master)
    input  axi_rsp_t        ds_resp_i,
    input  axi_req_t        ds_req_o,

    // Programming Interface (Slave) (AXI4 + ATOP => Reg IF)
    input  axi_req_slv_t    prog_req_i,
    input  axi_rsp_slv_t    prog_resp_o,

    input logic [(N_INT_VEC-1):0] wsi_wires_o
);

default clocking @(posedge clk_i); endclocking
default disable iff (~rst_ni);
`include "translation_req_axi_sva.sv"
`include "tranlation_completion_axi.sv"
`include "programing_interface_axi.sv"
`include "fifo_v3_sva.sv"
`include "translation_logic_wrapper_sva.sv"
`include "cut_point_assumptions/cut_point_assmp.sv"
// Translation request interface
tr_req_if #(.axi_req_iommu_t(axi_req_iommu_t),.axi_rsp_t(axi_rsp_t)) translation_req (clk_i, rst_ni, dev_tr_req_i, dev_tr_resp_o);

// Translation completion interface
axi_ds_tr_compl #(.axi_rsp_t(axi_rsp_t), .axi_req_t(axi_req_t)) translation_compl (clk_i, rst_ni, dev_comp_resp_i, dev_comp_req_o);

// Data structure interface
axi_ds_tr_compl #(.axi_rsp_t(axi_rsp_t), .axi_req_t(axi_req_t)) data_strcuture (clk_i, rst_ni, ds_resp_i, ds_req_o);

// Programming interface
prog_if #(axi_req_slv_t, axi_rsp_slv_t) programming_interface_axi(clk_i, rst_ni, prog_req_i, prog_resp_o);


//--------------------------------internal fifo verification---------------------------------------------


// data structure fifo
`define ds_intf_fifo riscv_iommu.i_rv_iommu_ds_if
fifo_v3_SVA ds_fifo_sva(clk_i, rst_ni,  `ds_intf_fifo.fifo_v3.flush_i,  0,  `ds_intf_fifo.fifo_v3.full_o,  `ds_intf_fifo.fifo_v3.empty_o, `ds_intf_fifo.fifo_v3.usage_o, `ds_intf_fifo.w_select, (`ds_intf_fifo.ds_req_o.aw_valid & `ds_intf_fifo.ds_resp_i.aw_ready), `ds_intf_fifo.w_select_fifo, (`ds_intf_fifo.ds_req_o.w_valid & `ds_intf_fifo.ds_resp_i.w_ready & `ds_intf_fifo.ds_req_o.w.last));

assmp_flush_0: assume property (!riscv_iommu.i_rv_iommu_ds_if.fifo_v3.flush_i);

// software interface fifo
`define soft_intf_fifo riscv_iommu.i_rv_iommu_sw_if_wrapper.i_rv_iommu_fq_handler
logic [rv_iommu::TTYP_LEN + rv_iommu::CAUSE_LEN + riscv::VLEN + riscv::SVX + 24 + 20 + 4 -1:0] soft_intf_data_o, soft_intf_data_i;
assign soft_intf_data_i = {`soft_intf_fifo.trans_type_i, `soft_intf_fifo.cause_code_i, `soft_intf_fifo.iova_i, `soft_intf_fifo.gpaddr_i, `soft_intf_fifo.did_i, `soft_intf_fifo.pv_i, `soft_intf_fifo.pid_i, `soft_intf_fifo.is_supervisor_i, `soft_intf_fifo.is_guest_pf_i, `soft_intf_fifo.is_implicit_i};

fifo_v3_SVA soft_intf_fifo_sva(clk_i, rst_ni, , 0, `soft_intf_fifo.is_full_o, `soft_intf_fifo.is_empty, `soft_intf_fifo.fifo_v3.usage_o, soft_intf_data_i, (`soft_intf_fifo.event_valid_i & !`soft_intf_fifo.edge_trigger_q), {`soft_intf_fifo.trans_type, `soft_intf_fifo.cause_code, `soft_intf_fifo.iova, `soft_intf_fifo.gpaddr, `soft_intf_fifo.did, `soft_intf_fifo.pv, `soft_intf_fifo.pid, `soft_intf_fifo.is_supervisor, `soft_intf_fifo.is_guest_pf, `soft_intf_fifo.is_implicit}, `soft_intf_fifo.is_idle);

endmodule