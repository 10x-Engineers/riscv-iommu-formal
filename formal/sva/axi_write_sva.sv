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

logic attr_selctor,attr_selctor_reg;
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

fifo #(.DEPTH_BITS(3),.DATA_WIDTH(64)) fifo_addr_m (clk_i, rst_ni, push, pop, `aw_addr, empty_addr, full_addr, fifo_addr);

fifo #(.DEPTH_BITS(3),.DATA_WIDTH(3)) fifo_size_m  (clk_i, rst_ni, push, pop, dev_tr_req_i.aw.size, empty_size, full_size, fifo_size);

fifo #(.DEPTH_BITS(3),.DATA_WIDTH(8)) fifo_len_m   (clk_i, rst_ni, push, pop, dev_tr_req_i.aw.len, empty_len, full_len, fifo_len);

fifo #(.DEPTH_BITS(3),.DATA_WIDTH(4)) fifo_id_m    (clk_i, rst_ni, push, pop, dev_tr_req_i.aw.id,  empty_id, full_id, fifo_id);


// -------- ----------------------------------aux code started for AWID----------------------------------------
logic [2**ariane_soc::IdWidth-1:0] id_seen ;

generate
for(genvar i = 0;  i < 2**ariane_soc::IdWidth; i++)
always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        id_seen[i] <= 0;    
    else if(aw_hsk && dev_tr_req_i.aw.id == i)
        id_seen[i] <= 1;

    else if(w_hsk && dev_tr_req_i.w.last && capture_id == i)
        id_seen[i]    <= 0;
end
endgenerate

generate
for(genvar i = 0; i < 2**ariane_soc::IdWidth; i++)
    assmp__7_diffrnt_awid:
    assume property (id_seen[i] |-> !dev_tr_req_i.aw_valid || dev_tr_req_i.aw.id != i);
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
assume property (counter_wlast == capture_len && `w_valid |-> dev_tr_req_i.w.last);

assmp_9_wlast: // if counter_wlast == capture_awlen, valid is high and symbolic_addr is seen then wlast must be asserted
assume property (!(counter_wlast == capture_len && `w_valid) |-> !dev_tr_req_i.w.last);   

// --------------------------------------aux code for wlast Ended---------------------------------------------


// --------------------------------------Aux code for unaligned strb Started----------------------

assmp_18_other_cycles_strb:
assume property (strb_unalig_other_tr |-> $countones(`strb) == 2**capture_size);

logic [`log_2_width_bytes - 1 : 0] mod_of_addr; // if data width is 4 bytes, then max awsize can be 4. by taking modulus of address with 4 the maximum rzlt is 3 so that's why log2(data_width)  
assign mod_of_addr = (capture_addr % (2**capture_size));

logic  strb_unalig_first_tr, strb_unalig_other_tr;
assign strb_unalig_first_tr = !strb_unalig_other_tr && !addrs_aligned && `w_valid;

always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        strb_unalig_other_tr <= 0;
        
    else if(dev_tr_req_i.w.last && w_hsk)
        strb_unalig_other_tr <= 0;

    else if((w_hsk && strb_unalig_first_tr) || strb_unalig_other_tr)
        strb_unalig_other_tr <= 1;
end

logic [`log_2_width_bytes - 1:0] addr_last_bits;
assign addr_last_bits = capture_addr[`log_2_width_bytes - 1:0];

generate
    for (genvar i = 1; i < ariane_axi_soc::StrbWidth - 1; i++ ) // this block will set lower bits of strb low for size = 3 starting from address last 3 bits in 64b address case
        assmp_26_8byte_unalig_strb:
        assume property (!addrs_aligned && (i < addr_last_bits) && (capture_size == 3) && strb_unalig_first_tr |-> !`strb[i]);
endgenerate

generate
    for (genvar i = 1; i < ariane_axi_soc::StrbWidth; i++ ) // this block will set Upper bits of strb high for size = 3 starting from address last 3 bits in 64b address case
        assmp_27_8byte_unalig_strb:
        assume property (!addrs_aligned && (i >= addr_last_bits) && (capture_size == 3) && strb_unalig_first_tr |-> `strb[i]);
endgenerate

generate // this block will set all other bits of strb 0, only the strb[address[2:0]:0] bit will be high
    for (genvar i = 0; i < ariane_axi_soc::StrbWidth ; i++)
        for (genvar j = 0; j < ariane_axi_soc::StrbWidth ; j++)
            if(i != j && (i % 2 != 0)) // checks should be on unaligned address
                assmp_28_2byte_unalig_strb:
                assume property (capture_size == 1 && !addrs_aligned && strb_unalig_first_tr && `strb[i] |-> !`strb[j]);
endgenerate

logic [`log_2_width_bytes-1:0] counter_unalign_addrs; 
always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        counter_unalign_addrs <= 0;

    else if (w_hsk && !not_1st_cycle_tr)
        counter_unalign_addrs <= capture_addr[`log_2_width_bytes-1:0] + 2**capture_size;

    else if (w_hsk)
        counter_unalign_addrs <= counter_unalign_addrs + 2**capture_size;
end

assmp_34_unaligned_other_cycle_strb:
assume property (!addrs_aligned && strb_unalig_other_tr && `w_valid |-> `strb[counter_unalign_addrs]);

// assrt_chcking_property:
// assert property (!addrs_aligned && strb_unalig_first_tr && `w_valid && capture_size == 1 |-> $countones(`strb)==1);


//-------------------------------idea dropped-------------------------
// logic [ariane_axi_soc::StrbWidth -1 : 0] delayed_strb, four_byte_unalig;
// always @(posedge clk_i or negedge rst_ni) begin
//     if(!rst_ni)
//         delayed_strb <= 0;
//     else 
//         delayed_strb <= `strb;
// end

// generate
// for (genvar i= 0; i < ariane_axi_soc::StrbWidth; i++)
//     always @(posedge clk_i or negedge rst_ni) begin
//         if(!rst_ni)
//             four_byte_unalig <= 0;

//         else if(capture_addr[`log_2_width_bytes-1 : 0] < 4) begin
//             if(i < 4 && i >= capture_addr[`log_2_width_bytes-1 : 0])
//                 four_byte_unalig[i] <= 1;
//             else
//                 four_byte_unalig[i] <= 0;
//         end
        
//         else if(capture_addr[`log_2_width_bytes - 1: 0] > 3) begin
//             if(i > 3 && (i >= capture_addr[`log_2_width_bytes-1 : 0]))
//                 four_byte_unalig[i] <= 1;
//             else
//                 four_byte_unalig[i] <= 0;
//         end
//     end
// endgenerate

// assmp_33_4_byte_unalig_strb:
// assume property (capture_size == 2 && !addrs_aligned && strb_unalig_first_tr |=> four_byte_unalig == delayed_strb);

// cov_checking_4_byte_unalig_strb:
// cover property (capture_size ==2 && strb_unalig_first_tr && !addrs_aligned ##1 w_hsk[*4]);

// --------------------------------------Aux code for unalligned strb ended--------------------


//--------------------------------------aux code for aligned consecutive strb bits started--------------------------------------

logic addrs_aligned;
assign addrs_aligned =  capture_addr % (2**capture_size) == 0;
logic not_1st_cycle_tr;
always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        not_1st_cycle_tr <= 0;
    else if(!not_1st_cycle_tr && w_hsk && dev_tr_req_i.w.last)
        not_1st_cycle_tr <= 0;
    else if(not_1st_cycle_tr && w_hsk && dev_tr_req_i.w.last)
        not_1st_cycle_tr <= 0;
    else if(!not_1st_cycle_tr && w_hsk)
        not_1st_cycle_tr <= 1;
end

logic starting_strb_bit;
assign starting_strb_bit = `strb[capture_addr[`log_2_width_bytes-1:0]];

logic [`log_2_width_bytes-1:0] counter_align_addrs; 
always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        counter_align_addrs <= 0;
    else if (w_hsk && !not_1st_cycle_tr)
        counter_align_addrs <= capture_addr[`log_2_width_bytes-1:0] + 2**capture_size;
    else if (w_hsk)
        counter_align_addrs <= counter_align_addrs + 2**capture_size;
end

assmp_15_wstrb: // if address is alligned according to awsize then no of ones in wstrb should be equal to the total no of valid bytes in wdata 
assume property (`w_valid && addrs_aligned |-> ($countones(`strb) == 2**capture_size));

// these constraints are for 64 bits data bus only 
generate 
    for (genvar i = 0; i < ariane_axi_soc::StrbWidth - 1; i = i + 2) begin:size_2
        assmp_21_consectuve_strb:
        assume property (capture_size == 1 && `strb[i] |-> `strb[i+1]);
    end
endgenerate

generate
    for (genvar i = 0; i < ariane_axi_soc::StrbWidth - 1; i = i + 4) begin:size_4
        if(i==0)
        assmp_22_consectuve_strb:
        assume property (capture_size == 2 && `strb[i] |-> `strb == 8'b00001111);
        else
        assmp_22_consectuve_strb:
        assume property (capture_size == 2 && `strb[i] |-> `strb == 8'b11110000);
    end
endgenerate

generate
    for (genvar i = 0; i < ariane_axi_soc::StrbWidth - 1; i = i + 8) begin:size_8
        assmp_23_consectuve_strb:
        assume property (capture_size == 3 && `strb[i] |-> `strb == 8'b11111111);
    end
endgenerate

assmp_24_starting_strb: // starting strb bit of first transfer in transaction
assume property (`w_valid && !not_1st_cycle_tr |-> starting_strb_bit);

assmp_25_aligned_other_cycle_strb:
assume property (addrs_aligned && not_1st_cycle_tr && `w_valid |-> `strb[counter_align_addrs]);

//--------------------------------------aux code for aligned consecutive strb bits ended--------------------------------------


//---------------------------------------Assumptions started-------------------------------------------------------
// property for handshake
property valid_stable(valid, ready, signal);
    valid && !ready |=> $stable(signal);
endproperty

// checks on the valid signals of write channels
assmp_1_w_channel_valid_stable:
assume property(valid_stable(`w_valid, dev_tr_resp_o.w_ready, dev_tr_req_i.w));

assmp_2_w_valid_stable:
assume property(valid_stable(`w_valid, dev_tr_resp_o.w_ready, `w_valid));

assmp_3_aw_channel_valid_stable:
assume property(valid_stable(dev_tr_req_i.aw_valid, dev_tr_resp_o.aw_ready, dev_tr_req_i.aw));

assmp_4_aw_valid_stable:
assume property(valid_stable(dev_tr_req_i.aw_valid, dev_tr_resp_o.aw_ready, dev_tr_req_i.aw_valid));

assmp_5_ar_channel_valid_stable:
assume property(valid_stable(dev_tr_req_i.ar_valid, dev_tr_resp_o.ar_ready, dev_tr_req_i.ar));

assmp_6_ar_valid_stable:
assume property(valid_stable(dev_tr_req_i.ar_valid, dev_tr_resp_o.ar_ready, dev_tr_req_i.ar_valid));


// assp_temp:
// assume property (!aw_hsk);
// cov_assmp_depth:
// cover property (w_hsk[*14]);

assmp_10_wvalid_dependency:
assume property (id_seen == 0 |-> !dev_tr_req_i.w_valid);

assmp_11_boundary_cross: // Burst shouldn't cross a 4kb address boundary
assume property (dev_tr_req_i.aw_valid |-> ((`aw_addr % 4096) + (2**dev_tr_req_i.aw.size + (dev_tr_req_i.aw.len + 1)) <= 4096));

generate
for (genvar i = 0; i <= `log_2_width_bytes ; i++) begin
    if(i!=2)  // will remove this later
    assmp_12_alligned_access_wrap: // address should be alligend if burst is wrap
    assume property (dev_tr_req_i.aw_valid && (dev_tr_req_i.aw.size == i) && (dev_tr_req_i.aw.burst == axi_pkg::BURST_WRAP) |-> ((`aw_addr % (2**i)) == 0));
end
endgenerate

assmp_13_length_wrap: // for wrap burst length shoud be 2,4,8 or 16
assume property (dev_tr_req_i.aw_valid && (dev_tr_req_i.aw.burst == axi_pkg::BURST_WRAP) |-> (dev_tr_req_i.aw.len == 2) || (dev_tr_req_i.aw.len == 4) || (dev_tr_req_i.aw.len == 8) || (dev_tr_req_i.aw.len == 16));

assmp_14_QOS: // A default value of 0b0000 indicates that the interface is not participating in any QoS scheme
assume property (dev_tr_req_i.aw_valid |-> dev_tr_req_i.aw.qos == 0);

assmp_19_reserved_burst: // burst == 2'b11 is reserved
assume property (dev_tr_req_i.aw.burst != 3);

assmp_20_awsize:
assume property (dev_tr_req_i.aw.size <= `log_2_width_bytes);

//-------------------------Assumptions ended-------------------------------

//-----------------assumptions need to be removed-------------------------
assmp1_remove_later:
assume property (`awsize != 2);
// also remove "if(i!=2)" from assmp_12_alligned_access_wrap when assmp1_remove_later will be remove 




//-------------------------Assumption and cover for chekcing fifo depth Started----------- 
// // assmp_fifo_depth:
// assume property (!w_hsk);
// cov_fifo_depth:
// cover property ((aw_hsk ##2 !aw_hsk )[*9]); 
// // from the "assmp_fifo_depth" and "cov_fifo_depth" it is clear that depth of fifo should be 8
//-------------------------Assumption and cover for chekcing fifo depth Ended--------------


//-------------------------Covers to verify the assumptions Started----------------------------------
// cov_stable_must_fail:
// cover property(`w_valid && !dev_tr_resp_o.w_ready ##1 $changed(dev_tr_req_i.w));

// cov_counter_last_must_fail_2:
// cover property (counter_wlast != capture_len && `w_valid && dev_tr_req_i.w.last);

// //  cov_wvalid_dependency_must_fail_3: // failing because excedding the outstanding req
// // cover property (combined_empty && aw_hsk && dev_tr_req_i.aw.len == 1 ##[1:$] combined_full && aw_hsk && !w_hsk);

// cov_same_awid_must_fail_4:
// cover property (combined_empty && dev_tr_req_i.aw.id == 8 && aw_hsk && !w_hsk ##1 dev_tr_req_i.aw.id == 8 && dev_tr_req_i.aw_valid);

// cov_diffrnt_awid_must_pass_5:
// cover property (dev_tr_req_i.aw.id == 1 && aw_hsk && !w_hsk ##1 dev_tr_req_i.aw.id == 0 && dev_tr_req_i.aw_valid);

// cov_strb_must_fail_5:
// cover property (capture_size == 1 && !attr_selctor && counter_wlast == 0 && w_hsk && $countones(`strb) > 2);

// cov_strb_must_pass:
// cover property (fifo_size == 3 && !attr_selctor && w_hsk && (fifo_addr%fifo&& $countones(`strb)==3);

// cov_confusion:
// cover property (1'b1 ##8 counter_wlast == capture_len && capture_len == 4 && `w_valid && dev_tr_req_i.w.last);

// cov_confusion2: 
// cover property (combined_empty && aw_hsk && dev_tr_resp_o.w_ready);


// cov_strb_assmp_must_fail:
// cover property (mod_of_addr == 0 && capture_addr[2:0] == 4 && w_hsk && !not_1st_cycle_tr && capture_size == 2 && `strb != 240 );


// cov_strb:
// cover property (!not_1st_cycle_tr && capture_size == 2 && addrs_aligned && w_hsk ##1 w_hsk[*3]);

//-------------------------Covers Ended------------------------------------


//------------------------assertion started-------------------------------
// r_channel_stable: // rvalid channel must be stable
// assert property(valid_stable(dev_tr_resp_o.r_valid, dev_tr_req_i.r_ready, dev_tr_resp_o.r));

// b_channel_stable:
// assert property(valid_stable(dev_tr_resp_o.b_valid, dev_tr_req_i.b_ready, dev_tr_resp_o.b.id));
//------------------------assertion ended--------------------------------


// bvalid:
// assert property (!combined_empty ##8 combined_empty && !aw_hsk |-> !b_hsk);

// assmp_fifo_depth:
// assume property (!w_hsk);

// cov_fifo_depth:
// cover property ((aw_hsk && !w_hsk ##1 !w_hsk ##1 !aw_hsk)[*9] ##1 b_hsk); 

// assume property (`w_valid);
// cov_combined_full:
// cover property (capture_size == 2 && combined_full);


// -------------------Cover and assumption to checking whether b_hsk can come before w_hsk and aw_hsk or not------------------ 
// assmp_fifo_depth:
// assume property (!w_hsk && !aw_hsk);

// cov_checking_b_hsk:
// cover property (b_hsk);



// --------------------------------------removed ---------------------------------------------
// generate
//     for (genvar i = 0; i < (ariane_axi_soc::StrbWidth)/2; i++) begin
//         assmp_29_4byte_unalig_strb_last_4_bits:
//         assume property (capture_size == 2 && !addrs_aligned && strb_unalig_first_tr && (`aw_addr[`log_2_width_bytes - 1 : 0] > i) |-> !`strb[i]);
        
//         if(i != 0)
//         assmp_30_4byte_unalig_strb_last_4_bits:
//         assume property (capture_size == 2 && !addrs_aligned && strb_unalig_first_tr && (`aw_addr[`log_2_width_bytes - 1 : 0] < i) |-> `strb[i]);
//     end
// endgenerate

// generate
//     for (genvar i = 4; i < ariane_axi_soc::StrbWidth - 1; i++) begin
//         assmp_31_4byte_unalig_strb_first_4_bits:
//         assume property (capture_size == 2 && !addrs_aligned && strb_unalig_first_tr && (`aw_addr[`log_2_width_bytes - 1 : 0] > i) |-> !`strb[i]);
        
//         assmp_32_4byte_unalig_strb_first_4_bits:
//         assume property (capture_size == 2 && !addrs_aligned && strb_unalig_first_tr && (`aw_addr[`log_2_width_bytes - 1 : 0] < i) |-> `strb[i]);
//     end
// endgenerate

// // instead of writing mod_of_addr, we can write addr[$clog2(data_in_bytes)-1:0]
// generate
// for (genvar i= 0; i < ariane_axi_soc::StrbWidth; i++) begin

// if(i != DATA_WIDTH_in_bytes-1) // this is the max of mod_of_addr
//     assmp_16_low_strb: // failing becasue assume max i = 7 and mod_of_addr max also 7 so at that time 7 can't be less than 7
//     assume property (strb_unalig_first_tr && (i < mod_of_addr) && `w_valid |-> !`strb[i]);

// if(i != 0) // no 0 was unreachable bcz 0 can't be greater than mod_of_addr and also strb_alligend_first can't be high when mod_of_addr is 0
//     assmp_17_high_strb:
//     assume property (strb_unalig_first_tr && (i >= mod_of_addr) && `w_valid |-> `strb[i]); 
// end
// endgenerate

//----------------------------------------------read channel started-----------------------------------

fifo_depth:
assume property (!r_hsk);

fifo_depth_cov:
cover property ((ar_hsk ##3 !ar_hsk)[*25]); 
// with 20 depth it is working
