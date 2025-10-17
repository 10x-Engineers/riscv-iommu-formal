module prog_if #(
    parameter type axi_req_slv_t = lint_wrapper::req_slv_t ,
    parameter type axi_rsp_slv_t = lint_wrapper::resp_slv_t
) (
    input clk_i, rst_ni,
    input  axi_req_slv_t  prog_req_i,
    input axi_rsp_slv_t prog_resp_o
);
    
    default clocking @(posedge clk_i); endclocking
    default disable iff (~rst_ni);  

//macros started
    `include "pr_intf_reg_read_write.sv"
    `include "fifo.sv"

    `define w_valid prog_req_i.w_valid

    `define ar_addr prog_req_i.ar.addr
    `define arid prog_req_i.ar.id
    `define arsize prog_req_i.ar.size
    `define arlen prog_req_i.ar.len
    `define arburst prog_req_i.ar.burst


    `define strb prog_req_i.w.strb
    `define w_data prog_req_i.w.data

    `define aw_addr prog_req_i.aw.addr
    `define awsize prog_req_i.aw.size
    `define awlen prog_req_i.aw.len
    `define awid prog_req_i.aw.id

    `define rlast prog_resp_o.r.last
    `define rdata prog_resp_o.r.data
    `define rid prog_resp_o.r.id

    `define bid prog_resp_o.b.id

    `define log_2_width_bytes $clog2(DATA_WIDTH_in_bytes)

//macros ended

localparam DATA_WIDTH_in_bytes = lint_wrapper::DataWidth / 8;

// Handshakes of all 5 channels
    logic ar_hsk, aw_hsk, w_hsk, b_hsk, r_hsk;

    // address read channel
    assign ar_hsk = prog_req_i.ar_valid && prog_resp_o.ar_ready;
    // read data channel
    assign r_hsk  = prog_resp_o.r_valid  &&  prog_req_i.r_ready;
    // address write channel
    assign aw_hsk = prog_req_i.aw_valid && prog_resp_o.aw_ready;
    // write data channel
    assign w_hsk  = `w_valid  &&  prog_resp_o.w_ready;
    // write response channel
    assign b_hsk  = prog_resp_o.b_valid  &&  prog_req_i.b_ready;
// Handshakes ended

logic [lint_wrapper::AddrWidth - 1:0] fifo_addr, capture_addr; 
logic [2:0] fifo_size, capture_size;
logic [7:0] fifo_len, capture_len;
logic [lint_wrapper::IdWidthSlv - 1:0] fifo_id, capture_id;

logic attr_selctor,attr_selctor_reg;
assign attr_selctor = (combined_empty && aw_hsk && w_hsk && counter_wlast == 0) || attr_selctor_reg;

always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        attr_selctor_reg <= 0;
    else if(w_hsk && prog_req_i.w.last)
        attr_selctor_reg <= 0;
    else if(attr_selctor)
        attr_selctor_reg <= 1;
end

assign capture_addr = attr_selctor ? `aw_addr : fifo_addr;
assign capture_size = attr_selctor ? prog_req_i.aw.size : fifo_size;
assign capture_len  = attr_selctor ? prog_req_i.aw.len  : fifo_len;
assign capture_id   = attr_selctor ? prog_req_i.aw.id   : fifo_id;

logic empty_len, empty_addr, empty_size, empty_id, full_len, full_addr, full_size, full_id; // empty and full signals of fifo
logic push, pop; // push and pop signals of fifo

logic combined_empty, combined_full;
assign combined_empty = empty_addr && empty_size && empty_len && empty_id;
assign combined_full  = full_addr && full_size && full_len && full_id;

assign push = aw_hsk && !combined_full && !(aw_hsk && w_hsk && combined_empty && counter_wlast == 0);
assign pop  = w_hsk && prog_req_i.w.last && !combined_empty;

fifo #(.DEPTH_BITS(3),.DATA_WIDTH(64)) fifo_addr_m (clk_i, rst_ni, push, pop, `aw_addr, empty_addr, full_addr, fifo_addr);

fifo #(.DEPTH_BITS(3),.DATA_WIDTH(3)) fifo_size_m  (clk_i, rst_ni, push, pop, prog_req_i.aw.size, empty_size, full_size, fifo_size);

fifo #(.DEPTH_BITS(3),.DATA_WIDTH(8)) fifo_len_m   (clk_i, rst_ni, push, pop, prog_req_i.aw.len, empty_len, full_len, fifo_len);

fifo #(.DEPTH_BITS(3),.DATA_WIDTH(4)) fifo_id_m    (clk_i, rst_ni, push, pop, prog_req_i.aw.id,  empty_id, full_id, fifo_id);


// -------- ----------------------------------aux code started for AWID----------------------------------------

    logic [2**lint_wrapper::IdWidthSlv-1:0] id_seen ;
    generate
    for(genvar i = 0;  i < 2**lint_wrapper::IdWidthSlv; i++)
    always @(posedge clk_i or negedge rst_ni) begin
        if(!rst_ni)
            id_seen[i] <= 0;    
        else if(aw_hsk && prog_req_i.aw.id == i)
            id_seen[i] <= 1;

        else if(w_hsk && prog_req_i.w.last && capture_id == i)
            id_seen[i]    <= 0;
    end
    endgenerate

    generate
    for(genvar i = 0; i < 2**lint_wrapper::IdWidthSlv; i++)
        assmp__7_diffrnt_awid:
        assume property (id_seen[i] |-> !prog_req_i.aw_valid || prog_req_i.aw.id != i);
    endgenerate

//-----------------------------------------------aux code ended for awid-----------------------------------


// --------------------------------------aux code for wlast started ------------------------------------------
    logic [8:0] counter_wlast; // when there is last transfer of burst, wlast must be high
    always @(posedge clk_i or negedge rst_ni) begin
        if(!rst_ni)
            counter_wlast <= 0;

        else if(w_hsk && (counter_wlast == capture_len))
            counter_wlast <= 0;

        else if(w_hsk)
            counter_wlast <= counter_wlast + 1;
    end

    assmp_8_wlast: // wlast can only be asserted if counter_wlast == capture_awlen and valid is high
    assume property (counter_wlast == capture_len && `w_valid |-> prog_req_i.w.last);

    assmp_9_wlast: 
    assume property (!(counter_wlast == capture_len && `w_valid) |-> !prog_req_i.w.last);   

// --------------------------------------aux code for wlast Ended---------------------------------------------


// --------------------------------------Aux code for unaligned strb Started----------------------
    logic [`log_2_width_bytes - 1 : 0] mod_of_addr; // if data width is 4 bytes, then max awsize can be 4. by taking modulus of address with 4 the maximum rzlt is 3 so that's why log2(data_width)  
    assign mod_of_addr = (capture_addr % (2**capture_size));

    logic  strb_unalig_first_tr, strb_unalig_other_tr;
    assign strb_unalig_first_tr = !strb_unalig_other_tr && !addrs_aligned && `w_valid;

    always @(posedge clk_i or negedge rst_ni) begin
        if(!rst_ni)
            strb_unalig_other_tr <= 0;

        else if(prog_req_i.w.last && w_hsk)
            strb_unalig_other_tr <= 0;

        else if((w_hsk && strb_unalig_first_tr) || strb_unalig_other_tr)
            strb_unalig_other_tr <= 1;
    end

    assmp_18_other_cycles_strb:
    assume property (strb_unalig_other_tr |-> $countones(`strb) == 2**capture_size);

    logic [`log_2_width_bytes - 1:0] addr_last_3_bits;
    assign addr_last_3_bits = capture_addr[`log_2_width_bytes - 1:0];

    generate
        for (genvar i = 1; i < lint_wrapper::StrbWidth - 1; i++ ) // this block will set lower bits of strb low for size = 3 starting from address last 3 bits in 64b address case
            assmp_26_8byte_unalig_strb:
            assume property (!addrs_aligned && (i < addr_last_3_bits) && (capture_size == 3) && strb_unalig_first_tr |-> !`strb[i]);
    endgenerate

    generate
        for (genvar i = 1; i < lint_wrapper::StrbWidth; i++ ) // this block will set Upper bits of strb high for size = 3 starting from address last 3 bits in 64b address case
            assmp_27_8byte_unalig_strb:
            assume property (!addrs_aligned && (i >= addr_last_3_bits) && (capture_size == 3) && strb_unalig_first_tr |-> `strb[i]);
    endgenerate

    generate // this block will set all other bits of strb 0, only the strb[address[2:0]:0] bit will be high
        for (genvar i = 0; i < lint_wrapper::StrbWidth ; i++)
            for (genvar j = 0; j < lint_wrapper::StrbWidth ; j++)
                if(i != j && (i % 2 != 0)) // checks should be on unaligned address
                    assmp_28_2byte_unalig_strb:
                    assume property (capture_size == 1 && !addrs_aligned && strb_unalig_first_tr && `strb[i] |-> !`strb[j]);
    endgenerate

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
    assume property (!addrs_aligned && strb_unalig_other_tr && `w_valid |-> `strb[counter_unalign_addrs]);

    // assrt_chcking_property:
    // assert property (!addrs_aligned && strb_unalig_first_tr && `w_valid && capture_size == 1 |-> $countones(`strb)==1);

//--------------------------------------aux code for unaligned consecutive strb bits ENDED--------------------------------------


//--------------------------------------aux code for aligned consecutive strb bits started--------------------------------------

    logic addrs_aligned;
    assign addrs_aligned =  capture_addr % (2**capture_size) == 0;
    logic first_cycle_tr_done;
    always @(posedge clk_i or negedge rst_ni) begin
        if(!rst_ni)
            first_cycle_tr_done <= 0;
        else if(!first_cycle_tr_done && w_hsk && prog_req_i.w.last)
            first_cycle_tr_done <= 0;
        else if(first_cycle_tr_done && w_hsk && prog_req_i.w.last)
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


//---------------------------------------Assumptions started-----------------------------

    // checks on the valid signals of write channels
    assmp_1_w_channel_valid_stable:
    assume property(valid_stable(`w_valid, prog_resp_o.w_ready, prog_req_i.w));

    assmp_2_w_valid_stable:
    assume property(valid_stable(`w_valid, prog_resp_o.w_ready, `w_valid));

    assmp_3_aw_channel_valid_stable:
    assume property(valid_stable(prog_req_i.aw_valid, prog_resp_o.aw_ready, prog_req_i.aw));

    assmp_4_aw_valid_stable:
    assume property(valid_stable(prog_req_i.aw_valid, prog_resp_o.aw_ready, prog_req_i.aw_valid));

    assmp_5_ar_channel_valid_stable:
    assume property(valid_stable(prog_req_i.ar_valid, prog_resp_o.ar_ready, prog_req_i.ar));

    assmp_6_ar_valid_stable:
    assume property(valid_stable(prog_req_i.ar_valid, prog_resp_o.ar_ready, prog_req_i.ar_valid));

    assmp_10_wvalid_dependency:
    assume property (id_seen == 0 |-> !prog_req_i.w_valid);

    assmp_11_boundary_cross: // Burst shouldn't cross a 4kb address boundary
    assume property (prog_req_i.aw_valid |-> ((`aw_addr % 4096) + (2**prog_req_i.aw.size * (prog_req_i.aw.len + 1)) <= 4096));

    generate
    for (genvar i = 0; i <= `log_2_width_bytes ; i++) begin
        if(i!=2)  // will remove this later
        assmp_12_alligned_access_wrap: // address should be alligend if burst is wrap
        assume property (prog_req_i.aw_valid && (prog_req_i.aw.size == i) && (prog_req_i.aw.burst == axi_pkg::BURST_WRAP) |-> ((`aw_addr % (2**i)) == 0));
    end
    endgenerate

    assmp_13_length_wrap: // for wrap burst length shoud be 2,4,8 or 16
    assume property (prog_req_i.aw_valid && (prog_req_i.aw.burst == axi_pkg::BURST_WRAP) |-> (prog_req_i.aw.len == 2) || (prog_req_i.aw.len == 4) || (prog_req_i.aw.len == 8) || (prog_req_i.aw.len == 16));

    assmp_14_QOS: // A default value of 0b0000 indicates that the interface is not participating in any QoS scheme
    assume property (prog_req_i.aw_valid |-> prog_req_i.aw.qos == 0);

    assmp_19_reserved_burst: // burst == 2'b11 is reserved
    assume property (prog_req_i.aw.burst != 3);

    assmp_20_awsize:
    assume property (prog_req_i.aw.size <= `log_2_width_bytes);


    generate
    for (genvar i = 0; i <= `log_2_width_bytes ; i++) begin
        if(i!=2)  // will remove this later
        assmp_21_alligned_access_wrap: // address should be alligend if burst is wrap
        assume property (prog_req_i.ar_valid && (prog_req_i.ar.size == i) && (prog_req_i.ar.burst == axi_pkg::BURST_WRAP) |-> ((`ar_addr % (2**i)) == 0));
    end
    endgenerate

    assmp_22_length_wrap: // for wrap burst length shoud be 2,4,8 or 16
    assume property (prog_req_i.ar_valid && (prog_req_i.ar.burst == axi_pkg::BURST_WRAP) |-> (prog_req_i.ar.len == 2) || (prog_req_i.ar.len == 4) || (prog_req_i.ar.len == 8) || (prog_req_i.ar.len == 16));

    assmp_23_reserved_burst: // burst == 2'b11 is reserved
    assume property (prog_req_i.ar.burst != 3);


    assmp_14_QOS_ar: // A default value of 0b0000 indicates that the interface is not participating in any QoS scheme
    assume property (prog_req_i.ar_valid |-> prog_req_i.ar.qos == 0);

//---------------------------------------Assumptions ended-------------------------------

//-----------------assumptions need to be removed later-------------------------
    assmp1_remove_later:
    assume property (`awsize != 2);
    // also remove "if(i!=2)" from assmp_12_alligned_access_wrap when assmp1_remove_later will be remove 


//------------------------assertion valid ready protocol started-------------------------------
    r_channel_stable: // rvalid channel must be stable
    assert property(valid_stable(prog_resp_o.r_valid, prog_req_i.r_ready, prog_resp_o.r));

    r_channel_stable_valid: // rvalid channel must be stable
    assert property(valid_stable(prog_resp_o.r_valid, prog_req_i.r_ready, prog_resp_o.r_valid));

    b_channel_stable_valid:
    assert property(valid_stable(prog_resp_o.b_valid, prog_req_i.b_ready, prog_resp_o.b_valid));

    b_channel_stable:
    assert property(valid_stable(prog_resp_o.b_valid, prog_req_i.b_ready, prog_resp_o.b));
//------------------------assertion valid ready protocol ended--------------------------------


//------------------------response channel started------------------------------------------
    logic [lint_wrapper::AddrWidth - 1:0] symbolic_addr; 
    logic [lint_wrapper::IdWidthSlv - 1:0] symbolic_id;

    assmp_stable_addr:
    assume property($stable(symbolic_addr));

    assmp_aligned_addr: // remove this assumption later as we are now checking only with size == 3 and aligned address
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
    assume property (aw_symbolic_sampled |-> !prog_req_i.aw_valid || (`aw_addr + (2**`awsize * (`awlen + 1))) < symbolic_addr);

    assmp_resp_counter_not_zero: // this assumption make sure that the aw_hsk wihtout b_hsk shouldn't exceed the total 14 time(can increase or decrease that counter according to our will). 
    assume property (resp_counter == 15 |->  resp_decr || !resp_incr); // will force that resp_incr will not come when resp_counter == 15

    assrt_bhsk_not_more_than_awhsk: // write_resp_hsk must not come more than the total number of aw_hsk
    assert property (prog_resp_o.b_valid && symbolic_id == `bid |-> resp_counter > 1);

//------------------------response channel Ended--------------------------------------------

//----------------------------------------------data read from symbolic addres Started------
    logic ready_to_see_bresp_of_symbolic, bresp_of_symbolic_seen;
    assign ready_to_see_bresp_of_symbolic = ((ready_to_sample_aw_symbolic && resp_counter == 1 && b_hsk) || (aw_symbolic_sampled && resp_counter == 2 && b_hsk) && !bresp_of_symbolic_seen);

    always @(posedge clk_i or negedge rst_ni)
        if(!rst_ni)
            bresp_of_symbolic_seen <= 0;
        else
            bresp_of_symbolic_seen <= ready_to_see_bresp_of_symbolic || bresp_of_symbolic_seen;

    logic ready_to_see_read_addr, read_addr_seen;

    assign ready_to_see_read_addr = (`arsize == 3) && `arid == symbolic_id && (`ar_addr == symbolic_addr) && ar_hsk && bresp_of_symbolic_seen && aw_symbolic_sampled && !read_addr_seen;
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

    assign read_incr = ar_hsk && (symbolic_id == `arid) && !read_addr_seen && !capability_addr_seen;
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

        else if(!read_first_cycle_tr_done && (`rid == symbolic_id) && r_hsk && prog_resp_o.r.last)
            read_first_cycle_tr_done <= 0;

        else if(read_first_cycle_tr_done && r_hsk && (`rid == symbolic_id) && prog_resp_o.r.last)
            read_first_cycle_tr_done <= 0;

        else if(!read_first_cycle_tr_done && (`rid == symbolic_id) && r_hsk)
            read_first_cycle_tr_done <= 1;

    logic must_read;
    assign must_read = (read_counter == 1) && (symbolic_id == `rid) && r_hsk && !read_first_cycle_tr_done && read_addr_seen;

    assrt_1st_tr_data_integrity:
    assert property (must_read |-> prog_resp_o.r.data == wdata_captured);
//----------------------------------------------data read from symbolic addres ended---------------------------


//----------------------------------------------Aux code for r_valid dependecny Started-----------------------------------
    // auxilary code to verify that r_valid should come after ar_valid and ar_ready
    int rvalid_counter;
    logic rvalid_cnt_incr, rvalid_cnt_decr;

    assign rvalid_cnt_incr = ar_hsk;
    assign rvalid_cnt_decr = r_hsk && prog_resp_o.r.last;

    always @(posedge clk_i or negedge rst_ni)
        if(!rst_ni)
            rvalid_counter <= 1;
        else
            rvalid_counter <= rvalid_counter + rvalid_cnt_incr - rvalid_cnt_decr;

    assrt_rvalid_depend: // r_valid mustn't come before ar_hsk
    assert property (prog_resp_o.r_valid |-> rvalid_counter > 1);

//----------------------------------------------Aux code for r_valid dependecny Ended-----------------------------------


endmodule