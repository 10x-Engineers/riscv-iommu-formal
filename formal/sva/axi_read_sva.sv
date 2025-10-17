`include "fifo.sv"

`define strb dev_tr_req_i.w.strb
`define w_valid dev_tr_req_i.w_valid
`define aw_addr dev_tr_req_i.aw.addr
`define awsize dev_tr_req_i.aw.size
`define log_2_width_bytes $clog2(DATA_WIDTH_in_bytes)

axi_req_iommu_t dev_tr_req_i;
axi_rsp_t dev_tr_resp_o;

localparam DATA_WIDTH_in_bytes = ariane_axi_soc::DataWidth / 8;

// Handshakes of all 5 channels 
logic ar_hsk, aw_hsk, w_hsk, b_hsk, r_hsk;

// address read channel
assign ar_hsk = dev_tr_req_i.ar_valid && dev_tr_resp_o.ar_ready;
// read data channel
assign r_hsk  = dev_tr_resp_o.r_valid  &&  dev_tr_req_i.r_ready;
// address write channel
assign aw_hsk = dev_tr_req_i.aw_valid && dev_tr_resp_o.aw_ready;
// write data channel
assign w_hsk  = `w_valid  &&  dev_tr_resp_o.w_ready;
// write response channel
assign b_hsk  = dev_tr_resp_o.b_valid  &&  dev_tr_req_i.b_ready;

logic [64-1:0] fifo_addr, capture_addr; // tbd include addrwidth in it(addrwidht = 64)
logic [2:0] fifo_size, capture_size;
logic [7:0] fifo_len, capture_len;
logic [4-1:0] fifo_id, capture_id; // tbd include (idwidth from ariance soc package)

logic attr_selctor, attr_selctor_reg;
assign attr_selctor = (combined_empty && aw_hsk && w_hsk && counter_wlast == 0) || attr_selctor_reg;

always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        attr_selctor_reg <= 0;
    else if(w_hsk && dev_tr_req_i.w.last)
        attr_selctor_reg <= 0;
    else if(attr_selctor)
        attr_selctor_reg <= 1;
end

assign capture_addr = attr_selctor ? `aw_addr : fifo_addr;
assign capture_size = attr_selctor ? dev_tr_req_i.aw.size : fifo_size;
assign capture_len  = attr_selctor ? dev_tr_req_i.aw.len  : fifo_len;
assign capture_id   = attr_selctor ? dev_tr_req_i.aw.id   : fifo_id;

logic empty_len, empty_addr, empty_size, empty_id, full_len, full_addr, full_size, full_id; // empty and full signals of fifo
logic push, pop; // push and pop signals of fifo

logic combined_empty, combined_full;
assign combined_empty = empty_addr && empty_size && empty_len && empty_id;
assign combined_full  = full_addr && full_size && full_len && full_id;

assign push = aw_hsk && !combined_full && !(aw_hsk && w_hsk && combined_empty && counter_wlast == 0);
assign pop  = w_hsk && dev_tr_req_i.w.last && !combined_empty;