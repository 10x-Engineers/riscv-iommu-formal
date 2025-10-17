module tr_req_if #(
    parameter type axi_req_iommu_t = lint_wrapper::req_iommu_t ,
    parameter type axi_rsp_t = lint_wrapper::resp_t
) (
    input                    clk_i,
    input                    rst_ni,
    input  axi_req_iommu_t  dev_tr_req_i,
    input  axi_rsp_t        dev_tr_resp_o
);

    default clocking @(posedge clk_i); endclocking
    default disable iff (~rst_ni);

`include "fifo.sv"
// write data channel macros
`define w_valid dev_tr_req_i.w_valid
`define strb dev_tr_req_i.w.strb
`define w_data dev_tr_req_i.w.data
// write response channel macros
`define bid dev_tr_resp_o.b.id
// address write channel macros
`define aw_addr dev_tr_req_i.aw.addr
`define awsize dev_tr_req_i.aw.size
`define awlen dev_tr_req_i.aw.len
`define awid dev_tr_req_i.aw.id
// address read channel macros
`define ar_addr dev_tr_req_i.ar.addr
`define arid dev_tr_req_i.ar.id
`define arsize dev_tr_req_i.ar.size
// read data channel macros
`define rlast dev_tr_resp_o.r.last
`define rdata dev_tr_resp_o.r.data
`define rid dev_tr_resp_o.r.id

localparam DATA_WIDTH_in_bytes = lint_wrapper::DataWidth / 8;
// TODO: instead of macro use parameter
`define log_2_width_bytes $clog2(DATA_WIDTH_in_bytes)

// Handshake of all 5 channels
logic ar_hsk, aw_hsk, w_hsk, b_hsk, r_hsk;
assign ar_hsk = dev_tr_req_i.ar_valid && dev_tr_resp_o.ar_ready;
assign r_hsk  = dev_tr_resp_o.r_valid  &&  dev_tr_req_i.r_ready;
assign aw_hsk = dev_tr_req_i.aw_valid && dev_tr_resp_o.aw_ready;
assign w_hsk  = `w_valid  &&  dev_tr_resp_o.w_ready;
assign b_hsk  = dev_tr_resp_o.b_valid  &&  dev_tr_req_i.b_ready;

logic [lint_wrapper::AddrWidth - 1:0] fifo_addr, capture_addr;
logic [lint_wrapper::IdWidth - 1:0] fifo_id, capture_id;
// TODO: Parametrized the data width of fifo_size, capture_size, fifo_len and capture_len
logic [2:0] fifo_size, capture_size;
logic [7:0] fifo_len, capture_len;

logic no_outstanding_axi_txn, no_outstanding_axi_txn_reg;
assign no_outstanding_axi_txn = (combined_empty && aw_hsk && w_hsk && counter_wlast == 0) || no_outstanding_axi_txn_reg;

always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        no_outstanding_axi_txn_reg <= 0;
    else if(w_hsk && dev_tr_req_i.w.last)
        no_outstanding_axi_txn_reg <= 0;
    else if(no_outstanding_axi_txn)
        no_outstanding_axi_txn_reg <= 1;
end

assign capture_addr = no_outstanding_axi_txn ? `aw_addr : fifo_addr;
assign capture_size = no_outstanding_axi_txn ? dev_tr_req_i.aw.size : fifo_size;
assign capture_len  = no_outstanding_axi_txn ? dev_tr_req_i.aw.len  : fifo_len;
assign capture_id   = no_outstanding_axi_txn ? dev_tr_req_i.aw.id   : fifo_id;

// tracking fifo's empty status
logic empty_len, empty_addr, empty_size, empty_id;
// tracking fifo's full status
full_len, full_addr, full_size, full_id;
logic push, pop; // push and pop signals of fifo

logic combined_empty, combined_full;
assign combined_empty = empty_addr && empty_size && empty_len && empty_id;
assign combined_full  = full_addr && full_size && full_len && full_id;

assign push = aw_hsk && !combined_full && !(aw_hsk && w_hsk && combined_empty && counter_wlast == 0);
assign pop  = w_hsk && dev_tr_req_i.w.last && !combined_empty;

fifo #(.DEPTH_BITS(3),.DATA_WIDTH(64)) fifo_addr_m  (clk_i, rst_ni, push, pop, `aw_addr, empty_addr, full_addr, fifo_addr);
fifo #(.DEPTH_BITS(3),.DATA_WIDTH(3))  fifo_size_m  (clk_i, rst_ni, push, pop, dev_tr_req_i.aw.size, empty_size, full_size, fifo_size);
fifo #(.DEPTH_BITS(3),.DATA_WIDTH(8))  fifo_len_m   (clk_i, rst_ni, push, pop, dev_tr_req_i.aw.len, empty_len, full_len, fifo_len);
fifo #(.DEPTH_BITS(3),.DATA_WIDTH(4))  fifo_id_m    (clk_i, rst_ni, push, pop, dev_tr_req_i.aw.id,  empty_id, full_id, fifo_id);

//////////////////////////////////Aux Code for Address Write Channels////////////////////////

// AWID must be unique
logic [2**lint_wrapper::IdWidth-1:0] id_seen ;
generate
for(genvar i=0; i < 2**lint_wrapper::IdWidth; i++)
always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        id_seen[i] <= 0;
    else if(aw_hsk && dev_tr_req_i.aw.id == i)
        id_seen[i] <= 1;
    else if(w_hsk && dev_tr_req_i.w.last && capture_id == i)
        id_seen[i] <= 0;
end
endgenerate

// WLAST signal modelling
logic [8:0] counter_wlast;
always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        counter_wlast <= 0;
    else if(w_hsk && (counter_wlast == capture_len))
        counter_wlast <= 0;
    else if(w_hsk)
        counter_wlast <= counter_wlast + 1;
end

logic  unaligned_first_beat, unaligned_follow_beat;
assign unaligned_first_beat = !unaligned_follow_beat && !addrs_aligned && `w_valid;

// if data width is 4 bytes, then max awsize can be 4. by taking modulus of address with 4 the maximum rzlt is 3 so that's why log2(data_width)
logic [`log_2_width_bytes - 1 : 0] mod_of_addr;
assign mod_of_addr = (capture_addr % (2**capture_size));

logic addrs_aligned;
assign addrs_aligned = (capture_addr % (2**capture_size)) == 0;

logic [`log_2_width_bytes - 1:0] addr_last_3_bits;
assign addr_last_3_bits = capture_addr[`log_2_width_bytes - 1:0];

always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        unaligned_follow_beat <= 0;
    else if(dev_tr_req_i.w.last && w_hsk)
        unaligned_follow_beat <= 0;
    else if((w_hsk && unaligned_first_beat) || unaligned_follow_beat)
        unaligned_follow_beat <= 1;
end

logic [`log_2_width_bytes-1:0] counter_unalign_addrs;
always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        counter_unalign_addrs <= 0;

    else if (w_hsk && !first_cycle_tr_done)
        counter_unalign_addrs <= capture_addr[`log_2_width_bytes-1:0] + 2**capture_size;

    else if (w_hsk)
        counter_unalign_addrs <= counter_unalign_addrs + 2**capture_size;
end

assmp_34_unaligned_other_cycle_strb:
assume property (!addrs_aligned && unaligned_follow_beat && `w_valid |-> `strb[counter_unalign_addrs]);

// assrt_chcking_property:
// assert property (!addrs_aligned && unaligned_first_beat && `w_valid && capture_size == 1 |-> $countones(`strb)==1);

// --------------------------------------Aux code for unalligned strb ended--------------------


//--------------------------------------aux code for aligned consecutive strb bits started--------------------------------------
logic first_cycle_tr_done;
always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        first_cycle_tr_done <= 0;
    else if(!first_cycle_tr_done && w_hsk && dev_tr_req_i.w.last)
        first_cycle_tr_done <= 0;
    else if(first_cycle_tr_done && w_hsk && dev_tr_req_i.w.last)
        first_cycle_tr_done <= 0;
    else if(!first_cycle_tr_done && w_hsk)
        first_cycle_tr_done <= 1;
end

logic starting_strb_bit;
assign starting_strb_bit = `strb[capture_addr[`log_2_width_bytes-1:0]];

logic [`log_2_width_bytes-1:0] counter_align_addrs;
always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        counter_align_addrs <= 0;
    else if (w_hsk && !first_cycle_tr_done)
        counter_align_addrs <= capture_addr[`log_2_width_bytes-1:0] + 2**capture_size;
    else if (w_hsk)
        counter_align_addrs <= counter_align_addrs + 2**capture_size;
end

assmp_15_wstrb: // if address is alligned according to awsize then no of ones in wstrb should be equal to the total no of valid bytes in wdata
assume property (`w_valid && addrs_aligned |-> ($countones(`strb) == 2**capture_size));

// these constraints are for 64 bits data bus only
generate
    for (genvar i = 0; i < lint_wrapper::StrbWidth - 1; i = i + 2) begin:size_2
        assmp_21_consectuve_strb:
        assume property (capture_size == 1 && `strb[i] |-> `strb[i+1]);
    end
endgenerate

generate
    for (genvar i = 0; i < lint_wrapper::StrbWidth - 1; i = i + 4) begin:size_4
        if(i==0)
        assmp_22_consectuve_strb:
        assume property (capture_size == 2 && `strb[i] |-> `strb == 8'b00001111);
        else
        assmp_22_consectuve_strb:
        assume property (capture_size == 2 && `strb[i] |-> `strb == 8'b11110000);
    end
endgenerate

generate
    for (genvar i = 0; i < lint_wrapper::StrbWidth - 1; i = i + 8) begin:size_8
        assmp_23_consectuve_strb:
        assume property (capture_size == 3 && `strb[i] |-> `strb == 8'b11111111);
    end
endgenerate

assmp_24_starting_strb: // starting strb bit of first transfer in transaction
assume property (`w_valid && !first_cycle_tr_done |-> starting_strb_bit);

assmp_25_aligned_other_cycle_strb:
assume property (addrs_aligned && first_cycle_tr_done && `w_valid |-> `strb[counter_align_addrs]);

//--------------------------------------aux code for aligned consecutive strb bits ended--------------------------------------
property valid_stable(valid, ready, signal);
    valid && !ready |=> $stable(signal);
endproperty

//---------------------------------------Assumptions started-------------------------------------------------------
// checks on the valid signals of write channels
assmp_1_w_channel_valid_stable: assume property(valid_stable(`w_valid, dev_tr_resp_o.w_ready, dev_tr_req_i.w));

assmp_2_w_valid_stable: assume property(valid_stable(`w_valid, dev_tr_resp_o.w_ready, `w_valid));

assmp_3_aw_channel_valid_stable: assume property(valid_stable(dev_tr_req_i.aw_valid, dev_tr_resp_o.aw_ready, dev_tr_req_i.aw));

assmp_4_aw_valid_stable: assume property(valid_stable(dev_tr_req_i.aw_valid, dev_tr_resp_o.aw_ready, dev_tr_req_i.aw_valid));

assmp_5_ar_channel_valid_stable: assume property(valid_stable(dev_tr_req_i.ar_valid, dev_tr_resp_o.ar_ready, dev_tr_req_i.ar));

assmp_6_ar_valid_stable: assume property(valid_stable(dev_tr_req_i.ar_valid, dev_tr_resp_o.ar_ready, dev_tr_req_i.ar_valid));

// Write Address Channel ID must be unique
generate
for(genvar i = 0; i < 2**lint_wrapper::IdWidth; i++)
    assmp_7_diffrnt_awid: assume property (id_seen[i] |-> dev_tr_req_i.aw.id != i);
endgenerate

// WLAST signal must be asserted while it is driving the final write transfer in the burst
assmp_8_wlast: assume property ((counter_wlast == capture_len) && `w_valid |-> dev_tr_req_i.w.last);

// WLAST signal must not be asserted if it isn't driving the final write transfer in the burst
assmp_9_wlast:
assume property (!(counter_wlast == capture_len && `w_valid) |-> !dev_tr_req_i.w.last);

assmp_10_wvalid_dependency:
assume property (id_seen == 0 |-> !dev_tr_req_i.w_valid);

assmp_11_boundary_cross_aw: // Burst shouldn't cross a 4kb address boundary
assume property (dev_tr_req_i.aw_valid |-> ((`aw_addr % 4096) + (2**dev_tr_req_i.aw.size * (dev_tr_req_i.aw.len + 1)) < 4096));

assmp_12_boundary_cross_ar: // Burst shouldn't cross a 4kb address boundary
assume property (dev_tr_req_i.ar_valid |-> ((`ar_addr % 4096) + (2**dev_tr_req_i.ar.size * (dev_tr_req_i.ar.len + 1)) < 4096));

generate
for (genvar i = 0; i <= `log_2_width_bytes ; i++) begin
    if(i!=2)  // will remove this later
    assmp_13_alligned_access_wrap: // address should be alligend if burst is wrap
    assume property (dev_tr_req_i.aw_valid && (dev_tr_req_i.aw.size == i) && (dev_tr_req_i.aw.burst == axi_pkg::BURST_WRAP) |-> ((`aw_addr % (2**i)) == 0));
end
endgenerate
// Wrap burst length for Write address channel can be 2,4,8 or 16
assmp_14_length_wrap_aw:
assume property (dev_tr_req_i.aw_valid && (dev_tr_req_i.aw.burst == axi_pkg::BURST_WRAP) |-> (dev_tr_req_i.aw.len == 1) || (dev_tr_req_i.aw.len == 3) || (dev_tr_req_i.aw.len == 7) || (dev_tr_req_i.aw.len == 15));
// Wrap burst length for Read address channel can be 2,4,8 or 16
assmp_15_length_wrap_ar:
assume property (dev_tr_req_i.ar_valid && (dev_tr_req_i.ar.burst == axi_pkg::BURST_WRAP) |-> (dev_tr_req_i.ar.len == 1) || (dev_tr_req_i.ar.len == 3) || (dev_tr_req_i.ar.len == 7) || (dev_tr_req_i.ar.len == 15));

assmp_16_QOS: // A default value of 0b0000 indicates that the interface is not participating in any QoS scheme
assume property (dev_tr_req_i.aw.qos == 0 && dev_tr_req_i.ar.qos == 0);

// only first unalign transaction needs strb
assmp_17_follow_beat_strb: assume property (unaligned_follow_beat |-> ($countones(`strb) == 2**capture_size));

generate
    for (genvar i = 1; i < lint_wrapper::StrbWidth - 1; i++ ) // this block will set lower bits of strb low for size = 3 starting from address last 3 bits in 64b address case
        assmp_18_8byte_unalig_strb: assume property (unaligned_first_beat && (i < addr_last_3_bits) && (capture_size == 3) |-> !`strb[i]);
endgenerate

generate
    for (genvar i = 1; i < lint_wrapper::StrbWidth; i++ ) // this block will set Upper bits of strb high for size = 3 starting from address last 3 bits in 64b address case
        assmp_19_8byte_unalig_strb: assume property (unaligned_first_beat && (i >= addr_last_3_bits) && (capture_size == 3) |-> `strb[i]);
endgenerate

generate // this block will set all other bits of strb 0, only the strb[address[2:0]:0] bit will be high
    for (genvar i = 0; i < lint_wrapper::StrbWidth ; i++)
        for (genvar j = 0; j < lint_wrapper::StrbWidth ; j++)
            if(i != j && (i % 2 != 0)) // checks should be on unaligned address
                assmp_20_2byte_unalig_strb: assume property (capture_size == 1 && unaligned_first_beat && `strb[i] |-> !`strb[j]);
endgenerate

// burst == 2'b11 is reserved
assmp_21_reserved_burst: assume property (dev_tr_req_i.aw.burst != 3 && dev_tr_req_i.ar.burst != 3);

assmp_22_awsize: assume property (dev_tr_req_i.aw.size <= `log_2_width_bytes && dev_tr_req_i.ar.size <= `log_2_width_bytes);

// aw_ids ---> 0 == CQ, 1 == FQ, and 2 == IG
// ar_ids ---> 0 == ptw, 1 == cdw, and 2 == CQ
assmp_23_id: assume property (dev_tr_req_i.aw.id <= 2 && dev_tr_req_i.ar.id <= 2);

//-------------------------Assumptions ended-------------------------------

//-----------------assumptions need to be removed later-------------------------
assmp1_remove_later:
assume property (`awsize != 2);
// also remove "if(i!=2)" from assmp_12_alligned_access_wrap when assmp1_remove_later will be remove


//------------------------assertion started-------------------------------
r_channel_stable: // rvalid channel must be stable
assert property(valid_stable(dev_tr_resp_o.r_valid, dev_tr_req_i.r_ready, dev_tr_resp_o.r));

r_channel_stable_valid: // rvalid channel must be stable
assert property(valid_stable(dev_tr_resp_o.r_valid, dev_tr_req_i.r_ready, dev_tr_resp_o.r_valid));

b_channel_stable_valid:
assert property(valid_stable(dev_tr_resp_o.b_valid, dev_tr_req_i.b_ready, dev_tr_resp_o.b_valid));

b_channel_stable:
assert property(valid_stable(dev_tr_resp_o.b_valid, dev_tr_req_i.b_ready, dev_tr_resp_o.b));
//------------------------assertion ended--------------------------------



//----------------------------------------------response channel started-----------------------------------
logic [lint_wrapper::AddrWidth - 1:0] symbolic_addr;
logic [lint_wrapper::IdWidth - 1:0] symbolic_id;

assmp_stable_addr:
assume property($stable(symbolic_addr));

assmp_aligned_addr: // remove this assumption later as we are now checking only with size == 3
assume property (symbolic_addr % 8 == 0);

assmp_stable_id:
assume property($stable(symbolic_id));

logic [3:0] resp_counter;
logic resp_incr, resp_decr;

assign resp_incr = aw_hsk && symbolic_id == `awid && !aw_symbolic_sampled; // incr with only one symbolic id and freeze the incr when aw_symbolic_sampled is seen
assign resp_decr = b_hsk  && symbolic_id == `bid; // decrement with only one symbolic id

always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni)
        resp_counter <= 1;
    else
        resp_counter <= resp_counter + resp_incr - resp_decr;

logic ready_to_sample_aw_symbolic, aw_symbolic_sampled;

// for simple awsize==3 and aligned address
assign ready_to_sample_aw_symbolic = aw_hsk && (`awsize == 3) && (symbolic_addr == `aw_addr) && (symbolic_id == `awid) && !aw_symbolic_sampled;

always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni)
        aw_symbolic_sampled <= 0;
    else
        aw_symbolic_sampled <= ready_to_sample_aw_symbolic || aw_symbolic_sampled;

assmp_id_not_equal_symbolic_id: //  id can't be equal to symbolic id, if symbolic id is seen once
assume property (aw_symbolic_sampled |-> `awid != symbolic_id);

assmp_addr_not_equal_symbolic_id: // aw_address can't be equal to symbolic address, if symbolic addr is seen once
assume property (aw_symbolic_sampled |-> (`aw_addr + (2**`awsize * (`awlen + 1))) < symbolic_addr);

assmp_resp_counter_not_zero: // this assumption make sure that the aw_hsk wihtout b_hsk shouldn't exceed the total 14 time(can increase or decrease that counter according to our will).
assume property (resp_counter == 15 |->  resp_decr || !resp_incr); // will force that resp_incr will not come when resp_counter == 15

assrt_bhsk_not_more_than_awhsk: // write_resp_hsk must not come more than the total number of aw_hsk
assert property (dev_tr_resp_o.b_valid && symbolic_id == `bid|-> resp_counter > 1);

//----------------------------------------------response channel Ended-----------------------------------

//----------------------------------------------read channel started-----------------------------------

// will verify it symbolically
// first we will verify it with the simple case which is size == 3(8 bytes) and address is alligned

logic ready_to_see_bresp_of_symbolic, bresp_of_symbolic_seen;
assign ready_to_see_bresp_of_symbolic = ((ready_to_sample_aw_symbolic && resp_counter == 1 && b_hsk) || (aw_symbolic_sampled && resp_counter == 2 && b_hsk) && !bresp_of_symbolic_seen);

always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni)
        bresp_of_symbolic_seen <= 0;
    else
        bresp_of_symbolic_seen <= ready_to_see_bresp_of_symbolic || bresp_of_symbolic_seen;

logic ready_to_see_read_addr, read_addr_seen;

assign ready_to_see_read_addr = (`arsize == 3) && (`arid == symbolic_id) && (`ar_addr == symbolic_addr) && ar_hsk && bresp_of_symbolic_seen && aw_symbolic_sampled && !read_addr_seen;

always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni)
        read_addr_seen <= 0;
    else
        read_addr_seen <= ready_to_see_read_addr || read_addr_seen;

logic ready_to_capture_w_data;
assign ready_to_capture_w_data = (capture_addr == symbolic_addr) && (capture_id == symbolic_id) && w_hsk && (aw_symbolic_sampled || ready_to_sample_aw_symbolic);

logic [lint_wrapper::DataWidth-1 : 0] wdata_captured;
always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni)
        wdata_captured <= 0;
    else if(ready_to_capture_w_data && !first_cycle_tr_done)
        wdata_captured <= `w_data;


logic read_incr, read_decr;
int read_counter;

assign read_incr = ar_hsk && (symbolic_id == `arid) && !read_addr_seen;
assign read_decr = r_hsk && `rlast && (symbolic_id == `rid) && !read_data_seen;

always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni)
        read_counter <= 0;
    else
        read_counter = read_counter + read_incr - read_decr;

logic ready_to_see_data, read_data_seen;
assign ready_to_see_data = (read_counter == 1) && read_decr && read_addr_seen; // to stop the read_decr for further asserting

always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni)
        read_data_seen <= 0;
    else
        read_data_seen <= ready_to_see_data || read_data_seen;

logic read_first_cycle_tr_done;
always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni)
        read_first_cycle_tr_done <= 0;

    else if(!read_first_cycle_tr_done && (`rid == symbolic_id) && r_hsk && dev_tr_resp_o.r.last)
        read_first_cycle_tr_done <= 0;

    else if(read_first_cycle_tr_done && r_hsk && (`rid == symbolic_id) && dev_tr_resp_o.r.last)
        read_first_cycle_tr_done <= 0;

    else if(!read_first_cycle_tr_done && (`rid == symbolic_id) && r_hsk)
        read_first_cycle_tr_done <= 1;

logic must_read;
assign must_read = (read_counter == 1) && (symbolic_id == `rid) && r_hsk && !read_first_cycle_tr_done && read_addr_seen;

assrt_1st_tr_data_integrity:
assert property (must_read |-> dev_tr_resp_o.r.data[2:0] == wdata_captured[2:0]);

// auxilary code to verify that r_valid should come after ar_valid and ar_ready
int rvalid_counter;
logic rvalid_cnt_incr, rvalid_cnt_decr;

assign rvalid_cnt_incr = ar_hsk;
assign rvalid_cnt_decr = r_hsk && dev_tr_resp_o.r.last;

always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni)
        rvalid_counter <= 1;
    else
        rvalid_counter <= rvalid_counter + rvalid_cnt_incr - rvalid_cnt_decr;

assrt_rvalid_depend: // r_valid mustn't come before ar_hsk
assert property (dev_tr_resp_o.r_valid |-> rvalid_counter > 1);
//----------------------------------------------read channel Ended-----------------------------------

endmodule
