//macros started
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

//.............................................capabilites register read started-------------------------------
    logic ready_to_see_capability_addr, capability_addr_seen;
    assign ready_to_see_capability_addr = (`arburst == 1) && (`arsize == 2) && `arlen == 1 && `arid == symbolic_id && (`ar_addr == 0) && ar_hsk && !capability_addr_seen;

    always @(posedge clk_i or negedge rst_ni)
        if(!rst_ni)
            capability_addr_seen <= 0;
        else 
            capability_addr_seen <= ready_to_see_capability_addr || capability_addr_seen;

    logic capibilty_must_read;
    assign capibilty_must_read = (read_counter == 1) && (symbolic_id == `rid) && r_hsk && $rose(read_first_cycle_tr_done) && !read_addr_seen && capability_addr_seen;

    assmp2_remove_later:
    assume property(`arlen < 16 && `awlen < 16); // if arlen is greater than 16, transaction will be automatically divided in multiple parts

    assmp3_remove_later:
    assume property (prog_req_i.ar.cache == 4'b0000 && prog_req_i.aw.cache == 4'b0000);

    //The IOMMU behavior for register accesses where the address is not aligned to the size of the access,
    // or if the access spans multiple registers, or if the size of the access is not 4 bytes or 8 bytes, is UNSPECIFIED
    assmp4_remove_later:
    assume property (`arsize == 2 && `ar_addr % 8 == 0); // will remove later

    // assmp5_remove_later:
    // assume property (`arid == symbolic_id |-> `ar_addr == 0 );

    assmp3_ar_size_less_than_3:
    assume property (`arsize < 3 && `ar_addr < 1024);

    assrt_2nd_capability:
    assert property (capibilty_must_read |-> prog_resp_o.r.data == 64'h0000_01f8_5002_0210);

//.............................................capabilites register read ended---------------------------------

