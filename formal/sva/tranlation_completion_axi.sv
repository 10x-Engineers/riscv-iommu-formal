// Copyright © 2025 Muhammad Hayat, 10xEngineers.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and limitations under the License.

module axi_ds_tr_compl #(
    parameter type  axi_req_t = lint_wrapper::req_t,
    /// AXI Full response struct type
    parameter type  axi_rsp_t = lint_wrapper::resp_t
)
(
    input clk_i, rst_ni,
    input  axi_rsp_t axi_ds_tr_compl_i,
    input axi_req_t axi_ds_tr_compl_o
);

`include "fifo.sv"
// Write channel macros
`define wlast_comp axi_ds_tr_compl_o.w.last
// Address write channel macros
`define aw_addr_comple axi_ds_tr_compl_o.aw.addr
`define awsize_comple axi_ds_tr_compl_o.aw.size
`define awlen_comple axi_ds_tr_compl_o.aw.len
`define awid_comple axi_ds_tr_compl_o.aw.id
// read data channel macros
`define rid_comple axi_ds_tr_compl_i.r.id
// write response channel macros
`define bid_comple axi_ds_tr_compl_i.b.id

default clocking @(posedge clk_i); endclocking
default disable iff (~rst_ni);

property valid_stable(valid, ready, signal);
    valid && !ready |=> $stable(signal);
endproperty

/////////////////////////AXI channel stable properties//////////////////////////

// If valid is high and ready is low then address read channel signals must be stable
assert_ar_channel_stable_tr_compl: assert property(valid_stable(axi_ds_tr_compl_o.ar_valid, axi_ds_tr_compl_i.ar_ready, axi_ds_tr_compl_o.ar));

// If valid is high and ready is low then address read valid must be stable
assert_ar_channel_stable_valid_tr_compl: assert property(valid_stable(axi_ds_tr_compl_o.ar_valid, axi_ds_tr_compl_i.ar_ready, axi_ds_tr_compl_o.ar_valid));

// If valid is high and ready is low then address write channel signals must be stable
assert_aw_channel_stable_tr_compl: assert property(valid_stable(axi_ds_tr_compl_o.aw_valid, axi_ds_tr_compl_i.aw_ready, axi_ds_tr_compl_o.aw));

// If valid is high and ready is low then address write valid must be stable
assert_aw_channel_stable_valid_tr_compl: assert property(valid_stable(axi_ds_tr_compl_o.aw_valid, axi_ds_tr_compl_i.aw_ready, axi_ds_tr_compl_o.aw_valid));

// If valid is high and ready is low then read channel signals must be stable
assert_r_channel_stable_tr_compl: assume property(valid_stable(axi_ds_tr_compl_i.r_valid, axi_ds_tr_compl_o.r_ready, axi_ds_tr_compl_i.r));

// If valid is high and ready is low then read channel valid must be stable
assert_r_channel_stable_valid_tr_compl: assume property(valid_stable(axi_ds_tr_compl_i.r_valid, axi_ds_tr_compl_o.r_ready, axi_ds_tr_compl_i.r_valid));

// If valid is high and ready is low then write response channel valid must be stable
assmp_b_channel_stable_valid_tr_compl: assume property(valid_stable(axi_ds_tr_compl_i.b_valid, axi_ds_tr_compl_o.b_ready, axi_ds_tr_compl_i.b_valid));

// If valid is high and ready is low then write response channel signals must be stable
assmp_b_channel_stable_tr_compl: assume property(valid_stable(axi_ds_tr_compl_i.b_valid, axi_ds_tr_compl_o.b_ready, axi_ds_tr_compl_i.b));

// Handshake of all 5 channels
logic ar_hsk_trnsl_compl, r_hsk_trnsl_compl, aw_hsk_trnsl_compl, w_hsk_trnsl_compl, b_hsk_trnsl_compl;
assign ar_hsk_trnsl_compl = axi_ds_tr_compl_o.ar_valid && axi_ds_tr_compl_i.ar_ready;
assign r_hsk_trnsl_compl = axi_ds_tr_compl_o.r_ready && axi_ds_tr_compl_i.r_valid;
assign aw_hsk_trnsl_compl = axi_ds_tr_compl_o.aw_valid && axi_ds_tr_compl_i.aw_ready;
assign w_hsk_trnsl_compl  = axi_ds_tr_compl_o.w_valid && axi_ds_tr_compl_i.w_ready;
assign b_hsk_trnsl_compl  = axi_ds_tr_compl_o.b_ready && axi_ds_tr_compl_i.b_valid;

//////////////////////////////////////Write channel modelling/////////////////////////

logic [lint_wrapper::AddrWidth - 1:0] fifo_addr_compl_w, capture_addr_compl_w;
// TODO: Parametrized the data width of fifo_size, capture_size, fifo_len and capture_lenp
logic [2:0] fifo_size_compl_w, capture_size_compl_w;
logic [7:0] fifo_len_compl_w, capture_len_compl_w;
logic [lint_wrapper::IdWidth - 1:0] fifo_id_compl_w, capture_id_compl_w;

// push and pop logic of fifo's
logic push_tr_compl_w, pop_tr_compl_w;
assign push_tr_compl_w = aw_hsk_trnsl_compl;
assign pop_tr_compl_w  = w_hsk_trnsl_compl && axi_ds_tr_compl_o.w.last;

logic combined_empty_tr_compl_w, combined_full_tr_compl_w;

assign combined_empty_tr_compl_w = empty_addr_tr_compl_w && empty_size_tr_compl_w && empty_len_tr_compl_w && empty_id_tr_compl_w;
assign combined_full_tr_compl_w  = full_addr_compl_w && full_size_compl_w && full_len_compl_w && full_id_compl_w;
// TODO: Replace multiple FIFOs with a single FIFO that stores a structured data type containing the address, size, length, and ID fields.
fifo #(.DEPTH_BITS(3),.DATA_WIDTH(64)) fifo_addr_tr_compl_w_m (clk_i, rst_ni, push_tr_compl_w, pop_tr_compl_w, `aw_addr_comple, empty_addr_tr_compl_w, full_addr_compl_w, fifo_addr_compl_w);
fifo #(.DEPTH_BITS(3),.DATA_WIDTH(3)) fifo_size_tr_compl_w_m (clk_i, rst_ni, push_tr_compl_w, pop_tr_compl_w, `awsize_comple, empty_size_tr_compl_w, full_size_compl_w, fifo_size_compl_w);
fifo #(.DEPTH_BITS(3),.DATA_WIDTH(8)) fifo_len_tr_compl_w_m (clk_i, rst_ni, push_tr_compl_w, pop_tr_compl_w, `awlen_comple, empty_len_tr_compl_w, full_len_compl_w, fifo_len_compl_w);
fifo #(.DEPTH_BITS(3),.DATA_WIDTH(4)) fifo_id_tr_compl_w_m (clk_i, rst_ni, push_tr_compl_w, pop_tr_compl_w,  `awid_comple,  empty_id_tr_compl_w, full_id_compl_w, fifo_id_compl_w);

logic no_outstanding_axi_txn;
assign no_outstanding_axi_txn = combined_empty_tr_compl_w && aw_hsk_trnsl_compl && w_hsk_trnsl_compl;

assign capture_addr_compl_w = no_outstanding_axi_txn ? `aw_addr_comple : fifo_addr_compl_w;
assign capture_size_compl_w = no_outstanding_axi_txn ? `awsize_comple  : fifo_size_compl_w;
assign capture_len_compl_w  = no_outstanding_axi_txn ? `awlen_comple   : fifo_len_compl_w;
assign capture_id_compl_w   = no_outstanding_axi_txn ? `awid_comple    : fifo_id_compl_w;

// modelling of write response channel
int write_cnt_compl[lint_wrapper::IdWidth -1 : 0];
generate
for (genvar i = 0; i < lint_wrapper::IdWidth; i++) begin
always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni)
        write_cnt_compl[i] <= 0;
    else if (capture_id_compl_w == i && w_hsk_trnsl_compl && `wlast_comp && `bid_comple == i && b_hsk_trnsl_compl)
        write_cnt_compl[i] <= write_cnt_compl[i];
    else if (capture_id_compl_w == i && w_hsk_trnsl_compl && `wlast_comp)
        write_cnt_compl[i] <= write_cnt_compl[i] + 1;
    else if (`bid_comple == i && b_hsk_trnsl_compl)
        write_cnt_compl[i] <= write_cnt_compl[i] - 1;

assmp_only_valid_bid: assume property (write_cnt_compl[i] == 0 |-> `bid != i);
end
endgenerate

int resp_counter_compl;
always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni)
        resp_counter_compl <= 1;
    else
        resp_counter_compl <= resp_counter_compl + aw_hsk_trnsl_compl - b_hsk_trnsl_compl;

// write_resp must not come more than the total number of aw_hsk_trnsl_compl
assmp_bhsk_not_more_than_awhsk: assume property (resp_counter_compl <= 1 |-> !axi_ds_tr_compl_i.b_valid );


/////////////////////////////////////read channel modelling////////////////////////////////////
logic push_tr_compl_r, pop_tr_compl_r;
logic fifo_addr_full_r, fifo_len_full_r, fifo_id_full_r, fifo_addr_empty_r, fifo_len_empty_r, fifo_id_empty_r;

logic fifo_combined_empty_r, fifo_combined_full_r;
assign fifo_combined_empty_r = fifo_addr_empty_r && fifo_len_empty_r && fifo_id_empty_r;
assign fifo_combined_full_r  = fifo_addr_full_r && fifo_len_full_r && fifo_id_full_r;

logic [lint_wrapper::AddrWidth - 1:0] fifo_addr_tr_compl_r;
logic [7:0] fifo_len_tr_compl_r;
logic [lint_wrapper::IdWidth - 1:0] fifo_id_tr_compl_r;

assign push_tr_compl_r = ar_hsk_trnsl_compl;
assign pop_tr_compl_r  = r_hsk_trnsl_compl && axi_ds_tr_compl_i.r.last;
// TODO: Replace multiple FIFOs with a single FIFO that stores a structured data type containing the address, size, length, and ID fields.
fifo #(.DEPTH_BITS(3),.DATA_WIDTH(64)) fifo_addr_tr_compl_m (clk_i, rst_ni, push_tr_compl_r, pop_tr_compl_r, axi_ds_tr_compl_o.ar.addr, fifo_addr_empty_r, fifo_addr_full_r, fifo_addr_tr_compl_r);
fifo #(.DEPTH_BITS(3),.DATA_WIDTH(8)) fifo_len_tr_compl_m  (clk_i, rst_ni, push_tr_compl_r, pop_tr_compl_r, axi_ds_tr_compl_o.ar.len, fifo_len_empty_r, fifo_len_full_r, fifo_len_tr_compl_r);
fifo #(.DEPTH_BITS(3),.DATA_WIDTH(8)) fifo_id_tr_compl_m  (clk_i, rst_ni, push_tr_compl_r, pop_tr_compl_r, axi_ds_tr_compl_o.ar.id, fifo_id_empty_r, fifo_id_full_r, fifo_id_tr_compl_r);

// Do not accept new transactions if there are already 8 outstanding transactions
// (threshold value can be adjusted as needed).
assmp_not_push_when_full: assume property (fifo_combined_full_r |-> !axi_ds_tr_compl_i.ar_ready);

// read data channel valid mustn't come before address read channel handshake
assmp_not_pop_when_empty: assume property (fifo_combined_empty_r |-> !axi_ds_tr_compl_i.r_valid);

// aw_ids ---> 0 == CQ, 1 == FQ, and 2 == IG
// ar_ids ---> 0 == ptw, 1 == cdw, and 2 == CQ
assmp_ids_less_than_2: assume property(axi_ds_tr_compl_i.r.id <= 2);

///////////////////////////////////////modelling for rlast////////////////////////

logic [8:0] counter_rlast; // when there is last transfer of burst, rlast must be high
always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        counter_rlast <= 0;
    else if(r_hsk_trnsl_compl && (counter_rlast == fifo_len_tr_compl_r))
        counter_rlast <= 0;
    else if(r_hsk_trnsl_compl)
        counter_rlast <= counter_rlast + 1;
end

// RLAST signal must be asserted while it is driving the final write transfer in the burst
assmp_rlast: assume property (counter_rlast == fifo_len_tr_compl_r && axi_ds_tr_compl_i.r_valid |-> axi_ds_tr_compl_i.r.last);

// RLAST signal must not be asserted if it isn't driving the final write transfer in the burst
assmp_not_rlast: assume property (!(counter_rlast == fifo_len_tr_compl_r && axi_ds_tr_compl_i.r_valid) |-> !axi_ds_tr_compl_i.r.last);

// rvalid must come after aw_hsk started
int read_counter;
always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni)
        read_counter <= 1;
    else
        read_counter <= read_counter + ar_hsk_trnsl_compl - (r_hsk_trnsl_compl && axi_ds_tr_compl_i.r.last);

// rvalid must come after ar_hsk
assmp_rvalid_dependency: assume property (axi_ds_tr_compl_i.r_valid |-> read_counter > 1);

////////////////////////////////////Overconstraints//////////////////////////

// overconstraint on read channel interleaving started
oc_not_interleaving_read: assume property (axi_ds_tr_compl_i.r_valid |-> fifo_id_tr_compl_r == `rid_comple);

endmodule
