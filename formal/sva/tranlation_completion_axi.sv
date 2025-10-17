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

// macros started
    `include "fifo.sv"
    `define w_valid_comple axi_ds_tr_compl_o.w_valid

    `define ar_addr_comple axi_ds_tr_compl_o.ar.addr
    `define arid_comple axi_ds_tr_compl_o.ar.id
    `define arsize_comple axi_ds_tr_compl_o.ar.size
    `define arlen_comple axi_ds_tr_compl_o.ar.len

    `define w_data_comp axi_ds_tr_compl_o.w.data
    `define wlast_comp axi_ds_tr_compl_o.w.last

    `define aw_addr_comple axi_ds_tr_compl_o.aw.addr
    `define awsize_comple axi_ds_tr_compl_o.aw.size
    `define awlen_comple axi_ds_tr_compl_o.aw.len
    `define awid_comple axi_ds_tr_compl_o.aw.id

    `define rlast_comple axi_ds_tr_compl_i.r.last
    `define rdata_comple axi_ds_tr_compl_i.r.data
    `define rid_comple axi_ds_tr_compl_i.r.id

    `define bid_comple axi_ds_tr_compl_i.b.id
// macros ended

    default clocking @(posedge clk_i); endclocking
    default disable iff (~rst_ni);

    property valid_stable(valid, ready, signal);
        valid && !ready |=> $stable(signal);
    endproperty

//------------------------stable assertion started-------------------------------

    assrt_ar_channel_stable_tr_compl: // arvalid channel must be stable
    assert property(valid_stable(axi_ds_tr_compl_o.ar_valid, axi_ds_tr_compl_i.ar_ready, axi_ds_tr_compl_o.ar));

    assrt_ar_channel_stable_valid_tr_compl: // rvalid channel must be stable
    assert property(valid_stable(axi_ds_tr_compl_o.ar_valid, axi_ds_tr_compl_i.ar_ready, axi_ds_tr_compl_o.ar_valid));

    assrt_aw_channel_stable_tr_compl: // awvalid channel must be stable
    assert property(valid_stable(axi_ds_tr_compl_o.aw_valid, axi_ds_tr_compl_i.aw_ready, axi_ds_tr_compl_o.aw));

    assrt_aw_channel_stable_valid_tr_compl: // awvalid must be stable
    assert property(valid_stable(axi_ds_tr_compl_o.aw_valid, axi_ds_tr_compl_i.aw_ready, axi_ds_tr_compl_o.aw_valid));

//------------------------stable assertion ended--------------------------------


//------------------------stable assumption started----------------------

    assrt_r_channel_stable_tr_compl: // rvalid channel must be stable
    assume property(valid_stable(axi_ds_tr_compl_i.r_valid, axi_ds_tr_compl_o.r_ready, axi_ds_tr_compl_i.r));

    assrt_r_channel_stable_valid_tr_compl: // rvalid channel must be stable
    assume property(valid_stable(axi_ds_tr_compl_i.r_valid, axi_ds_tr_compl_o.r_ready, axi_ds_tr_compl_i.r_valid));

    assmp_b_channel_stable_valid_tr_compl:
    assume property(valid_stable(axi_ds_tr_compl_i.b_valid, axi_ds_tr_compl_o.b_ready, axi_ds_tr_compl_i.b_valid));

    assmp_b_channel_stable_tr_compl:
    assume property(valid_stable(axi_ds_tr_compl_i.b_valid, axi_ds_tr_compl_o.b_ready, axi_ds_tr_compl_i.b));

//------------------------stable assumption ended-----------------------

// handshakes started
    logic ar_hsk_trnsl_compl, r_hsk_trnsl_compl;
    assign ar_hsk_trnsl_compl = axi_ds_tr_compl_o.ar_valid && axi_ds_tr_compl_i.ar_ready;
    assign r_hsk_trnsl_compl = axi_ds_tr_compl_o.r_ready && axi_ds_tr_compl_i.r_valid;

    logic aw_hsk_trnsl_compl, w_hsk_trnsl_compl, b_hsk_trnsl_compl;
    assign aw_hsk_trnsl_compl = axi_ds_tr_compl_o.aw_valid && axi_ds_tr_compl_i.aw_ready;
    assign w_hsk_trnsl_compl  = axi_ds_tr_compl_o.w_valid && axi_ds_tr_compl_i.w_ready;
    assign b_hsk_trnsl_compl  = axi_ds_tr_compl_o.b_ready && axi_ds_tr_compl_i.b_valid;
// handshakes ended

//-----------------Write channel started----------------------------

    logic [lint_wrapper::AddrWidth - 1:0] fifo_addr_compl_w, capture_addr_compl_w;
    logic [2:0] fifo_size_compl_w, capture_size_compl_w;
    logic [7:0] fifo_len_compl_w, capture_len_compl_w;
    logic [lint_wrapper::IdWidth - 1:0] fifo_id_compl_w, capture_id_compl_w;

    logic push_tr_compl_w, pop_tr_compl_w;
    assign push_tr_compl_w = aw_hsk_trnsl_compl;
    assign pop_tr_compl_w  = w_hsk_trnsl_compl && axi_ds_tr_compl_o.w.last;

    logic combined_empty_tr_compl_w, combined_full_tr_compl_w;

    assign combined_empty_tr_compl_w = empty_addr_tr_compl_w && empty_size_tr_compl_w && empty_len_tr_compl_w && empty_id_tr_compl_w;
    assign combined_full_tr_compl_w  = full_addr_compl_w && full_size_compl_w && full_len_compl_w && full_id_compl_w;

    fifo #(.DEPTH_BITS(3),.DATA_WIDTH(64)) fifo_addr_tr_compl_w_m (clk_i, rst_ni, push_tr_compl_w, pop_tr_compl_w, `aw_addr_comple, empty_addr_tr_compl_w, full_addr_compl_w, fifo_addr_compl_w);

    fifo #(.DEPTH_BITS(3),.DATA_WIDTH(3)) fifo_size_tr_compl_w_m (clk_i, rst_ni, push_tr_compl_w, pop_tr_compl_w, `awsize_comple, empty_size_tr_compl_w, full_size_compl_w, fifo_size_compl_w);

    fifo #(.DEPTH_BITS(3),.DATA_WIDTH(8)) fifo_len_tr_compl_w_m (clk_i, rst_ni, push_tr_compl_w, pop_tr_compl_w, `awlen_comple, empty_len_tr_compl_w, full_len_compl_w, fifo_len_compl_w);

    fifo #(.DEPTH_BITS(3),.DATA_WIDTH(4)) fifo_id_tr_compl_w_m (clk_i, rst_ni, push_tr_compl_w, pop_tr_compl_w,  `awid_comple,  empty_id_tr_compl_w, full_id_compl_w, fifo_id_compl_w);


    logic attr_selctor_compl_w;
    assign attr_selctor_compl_w = combined_empty_tr_compl_w && aw_hsk_trnsl_compl && w_hsk_trnsl_compl;

    assign capture_addr_compl_w = attr_selctor_compl_w ? `aw_addr_comple : fifo_addr_compl_w;
    assign capture_size_compl_w = attr_selctor_compl_w ? `awsize_comple : fifo_size_compl_w;
    assign capture_len_compl_w = attr_selctor_compl_w ? `awlen_comple : fifo_len_compl_w;
    assign capture_id_compl_w = attr_selctor_compl_w ? `awid_comple : fifo_id_compl_w;

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

    assmp_only_valid_bid:
    assume property (write_cnt_compl[i] == 0 |-> `bid != i);
    end

    endgenerate
//-----------------Write channel ended----------------------------


//-----------------response channel started--------------------------

    int resp_counter_compl;

    always @(posedge clk_i or negedge rst_ni)
        if(!rst_ni)
            resp_counter_compl <= 1;
        else
            resp_counter_compl <= resp_counter_compl + aw_hsk_trnsl_compl - b_hsk_trnsl_compl;

    assmp_bhsk_not_more_than_awhsk: // write_resp_hsk must not come more than the total number of aw_hsk_trnsl_compl
    assume property (resp_counter_compl < 2 |-> !axi_ds_tr_compl_i.b_valid );

//-----------------response channel ended--------------------------

//-----------------read channel started---------------------------
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

    fifo #(.DEPTH_BITS(3),.DATA_WIDTH(64)) fifo_addr_tr_compl_m (clk_i, rst_ni, push_tr_compl_r, pop_tr_compl_r, axi_ds_tr_compl_o.ar.addr, fifo_addr_empty_r, fifo_addr_full_r, fifo_addr_tr_compl_r);

    fifo #(.DEPTH_BITS(3),.DATA_WIDTH(8)) fifo_len__tr_compl_m  (clk_i, rst_ni, push_tr_compl_r, pop_tr_compl_r, axi_ds_tr_compl_o.ar.len, fifo_len_empty_r, fifo_len_full_r, fifo_len_tr_compl_r);

    fifo #(.DEPTH_BITS(3),.DATA_WIDTH(8)) fifo_id__tr_compl_m  (clk_i, rst_ni, push_tr_compl_r, pop_tr_compl_r, axi_ds_tr_compl_o.ar.id, fifo_id_empty_r, fifo_id_full_r, fifo_id_tr_compl_r);

    assmp_not_push_whn_full:
    assume property (fifo_combined_full_r |-> !axi_ds_tr_compl_i.ar_ready);

    assmp_not_pop_when_empty: // rvalid dependency
    assume property (fifo_combined_empty_r |-> !axi_ds_tr_compl_i.r_valid);

    assmp_ids_less_than_2:
    assume property(axi_ds_tr_compl_i.r.id <= 2);

//-----------------read channel ended---------------------------


// --------------------------------------aux code for rlast started ------------------------------------------
    logic [8:0] counter_rlast; // when there is last transfer of burst, rlast must be high
    always @(posedge clk_i or negedge rst_ni) begin
        if(!rst_ni)
            counter_rlast <= 0;

        else if(r_hsk_trnsl_compl && (counter_rlast == fifo_len_tr_compl_r))
            counter_rlast <= 0;

        else if(r_hsk_trnsl_compl)
            counter_rlast <= counter_rlast + 1;
    end

    assmp_8_rlast: // wlast can only be asserted if counter_rlast == capture_arlen and valid is high
    assume property (counter_rlast == fifo_len_tr_compl_r && axi_ds_tr_compl_i.r_valid |-> axi_ds_tr_compl_i.r.last);

    assmp_9_rlast: // if counter_rlast == capture_arlen, valid is high and symbolic_addr is seen then wlast must be asserted
    assume property (!(counter_rlast == fifo_len_tr_compl_r && axi_ds_tr_compl_i.r_valid) |-> !axi_ds_tr_compl_i.r.last);

// --------------------------------------aux code for rlast Ended---------------------------------------------

// overconstraint on read channel interleaving started
    assmp_not_interleaving_read:
    assume property (axi_ds_tr_compl_i.r_valid |-> fifo_id_tr_compl_r == `rid_comple);

// overconstraint on read channel interleaving ended

// rvalid must come after aw_hsk started
    int read_counter;

    always @(posedge clk_i or negedge rst_ni)
        if(!rst_ni)
            read_counter <= 1;
        else
            read_counter <= read_counter + ar_hsk_trnsl_compl - (r_hsk_trnsl_compl && axi_ds_tr_compl_i.r.last);

    assmp_rvalid_dependency:
    assume property (axi_ds_tr_compl_i.r_valid |-> read_counter > 1);
// rvalid must come after aw_hsk ended

endmodule
