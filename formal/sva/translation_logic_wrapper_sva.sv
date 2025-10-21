// Copyright © 2025 Muhammad Hayat, 10xEngineers.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and limitations under the License.

// macro for axi channels
`define ar_addr dev_tr_req_i.ar.addr
`define aw_addr dev_tr_req_i.aw.addr
`define ds_r_channel ds_resp_i.r

// address read/write channel handshake flag
logic aw_or_ar_hsk;
assign aw_or_ar_hsk = (translation_req.ar_hsk || translation_req.aw_hsk);

// reserved bits
logic ar_did_wider, aw_did_wider;
assign ar_did_wider = ((riscv_iommu.ddtp.iommu_mode.q == 2 && |dev_tr_req_i.ar.stream_id[23:6]) || (riscv_iommu.ddtp.iommu_mode.q == 3 && |dev_tr_req_i.ar.stream_id[23:15])) && translation_req.ar_hsk;
assign aw_did_wider = ((riscv_iommu.ddtp.iommu_mode.q == 2 && |dev_tr_req_i.aw.stream_id[23:6]) || (riscv_iommu.ddtp.iommu_mode.q == 3 && |dev_tr_req_i.aw.stream_id[23:15])) && translation_req.aw_hsk;

// write request has priority over read request
logic aw_seen_before;
always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        aw_seen_before <= 0;
    else if(aw_seen_before && translation_req.aw_hsk)
        aw_seen_before <= 0;
    else if(dev_tr_req_i.aw_valid && !dev_tr_req_i.ar_valid)
        aw_seen_before <= 1;
end

logic [riscv::VLEN - 1 : 0] selected_addr;
assign selected_addr = aw_seen_before ? dev_tr_req_i.aw.addr : (dev_tr_req_i.ar_valid ? dev_tr_req_i.ar.addr :(dev_tr_req_i.aw_valid ? dev_tr_req_i.aw.addr : 0));

logic [19:0] selected_pid;
assign selected_pid = aw_seen_before ? dev_tr_req_i.aw.substream_id : (dev_tr_req_i.ar_valid ? dev_tr_req_i.ar.substream_id :(dev_tr_req_i.aw_valid ? dev_tr_req_i.aw.substream_id : 0));

logic [23:0] selected_did;
assign selected_did = aw_seen_before ? dev_tr_req_i.aw.stream_id : (dev_tr_req_i.ar_valid ? dev_tr_req_i.ar.stream_id :(dev_tr_req_i.aw_valid ? dev_tr_req_i.aw.stream_id : 0));

logic priv_transac;
assign priv_transac = aw_seen_before ? dev_tr_req_i.aw.prot[0] : (dev_tr_req_i.ar_valid ? dev_tr_req_i.ar.prot[0] :(dev_tr_req_i.aw_valid ? dev_tr_req_i.aw.prot[0] : 0));

enum logic [1:0] {NONE, UNTRANSLATED_RX, UNTRANSLATED_R, UNTRANSLATED_W} trans_type;
assign trans_type = aw_seen_before ? UNTRANSLATED_W : (dev_tr_req_i.ar_valid ? (dev_tr_req_i.ar.prot[2] ? UNTRANSLATED_RX : UNTRANSLATED_R) : (dev_tr_req_i.aw_valid ? UNTRANSLATED_W : NONE));

logic selected_pv;
assign selected_pv = aw_seen_before ? dev_tr_req_i.aw.ss_id_valid : (dev_tr_req_i.ar_valid ? dev_tr_req_i.ar.ss_id_valid :(dev_tr_req_i.aw_valid ? dev_tr_req_i.aw.ss_id_valid : 0));

// non-leaf ddte reserved bits
logic ddte_rsrv_bits;
assign ddte_rsrv_bits = (|`ds_r_channel.data[9:1] || |`ds_r_channel.data[63:54]);

logic last_beat_cdw;
assign last_beat_cdw = ds_resp_i.r.last && ds_resp_i.r_valid && ds_resp_i.r.id == 1;

/////////////////////////////////////aux code CDW/////////////////////////
// The following auxiliary code tells us what level we are at while doing the device directory walk.
logic [1:0] counter_non_leaf;
always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni || riscv_iommu.trans_error)
        counter_non_leaf <= 0;
    else if(counter_non_leaf == 1 && ddtp.iommu_mode.q == 3 && last_beat_cdw && data_strcuture.r_hsk_trnsl_compl) // ddtlevel 2
        counter_non_leaf <= 0;
    else if(counter_non_leaf == 2 && ddtp.iommu_mode.q == 4 && last_beat_cdw && data_strcuture.r_hsk_trnsl_compl) // ddtlevel 3
        counter_non_leaf <= 0;
    else if(ddtp.iommu_mode.q > 2 && data_strcuture.r_hsk_trnsl_compl && last_beat_cdw)
        counter_non_leaf <= counter_non_leaf + 1;

// The following auxiliary code indicates which device context structure is being accessed.
logic [1:0] counter_dc;
always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni )
        counter_dc <= 0;
    else if(aw_or_ar_hsk)
        counter_dc <= 0;
    else if(counter_dc == 3 && !aw_or_ar_hsk)
        counter_dc <= 3;
    else if((ddtp.iommu_mode.q == 2 || ((counter_non_leaf == 2 && ddtp.iommu_mode.q == 4) || (counter_non_leaf == 1 && ddtp.iommu_mode.q == 3) && !riscv_iommu.trans_error)) && data_strcuture.r_hsk_trnsl_compl && ds_resp_i.r.id == 1 && !ddtc_hit_q)
        counter_dc <= counter_dc + 1;

logic ddte_accessed;
assign ddte_accessed = counter_dc == 0 && ((riscv_iommu.ddtp.iommu_mode.q == 4 && counter_non_leaf < 2) || (!selected_did[23:15] && riscv_iommu.ddtp.iommu_mode.q == 3 && !counter_non_leaf));

// The following flags indicate which error message the IOMMU must send.
logic ready_to_capture_ddt_entry_invalid, ddt_entry_invalid_captured;
logic ready_to_capture_ddt_data_corruption, ddt_data_corruption_captured;
logic ready_to_capture_ddte_misconfig_rsrv_bits, ddte_misconfig_rsrv_captured;

assign ready_to_capture_ddt_entry_invalid        = (!pc_fsc_active && !pc_ta_active) && ds_resp_i.r.resp == axi_pkg::RESP_OKAY && ddte_accessed && !ds_resp_i.r.data[0] && data_strcuture.r_hsk_trnsl_compl && ds_resp_i.r.id == 1 && !ddt_entry_invalid_captured;

assign ready_to_capture_ddt_data_corruption      = !(pid_wider || ar_did_wider || aw_did_wider) && (!pc_fsc_active && !pc_ta_active) && !ddt_entry_invalid_captured && !ddte_misconfig_rsrv_captured && ds_resp_i.r.resp != axi_pkg::RESP_OKAY && data_strcuture.r_hsk_trnsl_compl && ds_resp_i.r.id == 1 && !ddt_data_corruption_captured;
assign ready_to_capture_ddte_misconfig_rsrv_bits = !pdtc_miss_q && !pc_fsc_active && !pc_ta_active && !ddt_entry_invalid_captured && ds_resp_i.r.data[0] && !ddt_data_corruption_captured && ddte_accessed && ds_resp_i.r.id == 1 && ds_resp_i.r.resp == axi_pkg::RESP_OKAY && data_strcuture.r_hsk_trnsl_compl && ddte_rsrv_bits;

// tc.pdtv, tc.sxl
logic tc_pdtv, tc_pdtv_seen, tc_sxl, tc_sxl_seen ;
assign tc_pdtv = dc_tc_active && dc_tc_q.pdtv && !tc_pdtv_seen;
assign tc_sxl  = dc_tc_active && dc_tc_q.sxl && !tc_sxl_seen;

always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
        ddt_entry_invalid_captured   <= 0;
        ddt_data_corruption_captured <= 0;
        tc_pdtv_seen                 <= 0;
        tc_sxl_seen                  <= 0;
    end
    else if(ds_resp_i.r.last && data_strcuture.r_hsk_trnsl_compl && ds_resp_i.r.id == 1) begin
        ddt_entry_invalid_captured   <= 0;
        ddt_data_corruption_captured <= 0;
        tc_pdtv_seen                 <= 0;
        tc_sxl_seen                  <= 0;
    end
    else begin
        ddt_entry_invalid_captured    <= ddt_entry_invalid_captured   || ready_to_capture_ddt_entry_invalid;
        ddt_data_corruption_captured  <= ddt_data_corruption_captured || ready_to_capture_ddt_data_corruption;
        tc_pdtv_seen                  <= tc_pdtv_seen || tc_pdtv;
        tc_sxl_seen                   <= tc_sxl_seen  || tc_sxl;
    end
end

always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        ddte_misconfig_rsrv_captured <= 0;
    else if(last_beat_cdw && data_strcuture.r_hsk_trnsl_compl &&  ((ready_to_capture_ddte_misconfig_rsrv_bits || ddte_misconfig_rsrv_captured) || (riscv_iommu.ddtp.iommu_mode.q == 4 && counter_non_leaf == 2) || (riscv_iommu.ddtp.iommu_mode.q == 3 && counter_non_leaf == 1)))
        ddte_misconfig_rsrv_captured <= 0;
    else
        ddte_misconfig_rsrv_captured <= ddte_misconfig_rsrv_captured || ready_to_capture_ddte_misconfig_rsrv_bits;
end

// These flags indicate which device context structure is being accessed.
logic dc_tc_active, dc_iohgatp_active, dc_ta_active, dc_fsc_active;

assign dc_tc_active      = !riscv_iommu.trans_error && ds_resp_i.r.id == 1 && ds_resp_i.r_valid && !counter_dc && (riscv_iommu.ddtp.iommu_mode.q == 2 || (counter_non_leaf == 2 && ddtp.iommu_mode.q == 4) || (counter_non_leaf == 1 && ddtp.iommu_mode.q == 3)) ;
assign dc_iohgatp_active = ds_resp_i.r.id == 1 && ds_resp_i.r_valid && counter_dc == 1;
assign dc_ta_active      = ds_resp_i.r.id == 1 && ds_resp_i.r_valid && counter_dc == 2;
assign dc_fsc_active     = ds_resp_i.r.id == 1 && ds_resp_i.r_valid && counter_dc == 3 && !dc_ended_captured;

// device context structures
rv_iommu::tc_t      dc_tc_q;
rv_iommu::iohgatp_t dc_iohgatp_q;
rv_iommu::dc_ta_t   dc_ta_q;
rv_iommu::fsc_t     dc_fsc_q;

assign dc_tc_q      = dc_tc_active      ? ds_resp_i.r.data : 0;
assign dc_iohgatp_q = dc_iohgatp_active ? ds_resp_i.r.data : 0;
assign dc_ta_q      = dc_ta_active      ? ds_resp_i.r.data : 0;
assign dc_fsc_q     = dc_fsc_active     ? ds_resp_i.r.data : 0;

logic dc_tc_not_valid, dc_tc_not_valid_captured, ready_to_capture_data_corruption, dc_data_corruption_captured;
assign ready_to_capture_data_corruption = !pdtc_miss_q && !dc_ended_captured && (dc_tc_active || counter_dc != 0 ) && ds_resp_i.r.id == 1 && ds_resp_i.r_valid && ds_resp_i.r.resp != axi_pkg::RESP_OKAY && !dc_data_corruption_captured;
assign dc_tc_not_valid                  = dc_tc_active && ds_resp_i.r.resp == axi_pkg::RESP_OKAY && !dc_tc_q.v && !dc_tc_not_valid_captured;

// Different device context configuration checks
logic iohgatp_unsupported_mode, iohgatp_ppn_not_align, dc_rsrv_bits_high, tc_wrong_bits_high, iosatp_invalid;

assign dc_rsrv_bits_high        = (dc_tc_active && (|dc_tc_q.reserved_1 || |dc_tc_q.reserved_2)) || (dc_ta_active && (|dc_ta_q.reserved_1 || |dc_ta_q.reserved_2));
assign tc_wrong_bits_high       =  dc_tc_q.en_ats || dc_tc_q.en_pri || dc_tc_q.t2gpa || dc_tc_q.prpr || dc_tc_q.sade || dc_tc_q.gade || (dc_tc_active && ((riscv_iommu.fctl.be != dc_tc_q.sbe) || (riscv_iommu.fctl.gxl != dc_tc_q.sxl) || (!dc_tc_q.pdtv && dc_tc_q.dpe)));
assign iohgatp_unsupported_mode = riscv_iommu.fctl.gxl ? (dc_iohgatp_active && dc_iohgatp_q.mode != 0) : (dc_iohgatp_active && dc_iohgatp_q.mode != 0 && dc_iohgatp_q.mode != 8);
assign iohgatp_ppn_not_align    = dc_iohgatp_active && dc_iohgatp_q.mode != 0 && |dc_iohgatp_q.ppn[1:0];
assign iosatp_invalid           = !ready_to_capture_pdtv_zero && !dc_tc_not_valid_captured && !dc_data_corruption_captured && !dc_misconfig_captured && dc_fsc_active && ds_resp_i.r.resp == axi_pkg::RESP_OKAY && (|dc_fsc_q.reserved || (tc_pdtv_seen && (dc_fsc_q.mode inside {[4:15]})) || (!tc_pdtv_seen && (tc_sxl_seen ? dc_fsc_q.mode != 0 : !(!dc_fsc_q.mode || dc_fsc_q.mode == 8))));

// flag to capture the device context misconfiguration error
logic ready_to_capture_dc_misconfig, dc_misconfig_captured, misconfig_checks;
assign misconfig_checks         = (iosatp_invalid && MSITrans != rv_iommu::MSI_DISABLED) || tc_wrong_bits_high || iohgatp_unsupported_mode || iohgatp_ppn_not_align || dc_rsrv_bits_high;
assign ready_to_capture_dc_misconfig = (!dc_pc_with_data_corruption_captured && !dc_pc_with_data_corruption) && !dc_tc_not_valid_captured && ((dc_tc_active && dc_tc_q.v) || counter_dc !=0) && ds_resp_i.r.resp == axi_pkg::RESP_OKAY &&  misconfig_checks;

// InclPc=0 and tc.pdtv=1 can't be true at the same time
logic ready_to_capture_pdtv_zero, pdtv_zero_captured;
assign ready_to_capture_pdtv_zero    = !dc_tc_not_valid && (!dc_pc_with_data_corruption_captured && !dc_pc_with_data_corruption) && (!InclPC && dc_tc_q.pdtv) && dc_tc_active;

always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
        dc_tc_not_valid_captured       <= 0;
        dc_data_corruption_captured    <= 0;
        dc_misconfig_captured          <= 0;
        pdtv_zero_captured             <= 0;
    end
    else if(counter_dc == 3 && data_strcuture.r_hsk_trnsl_compl && last_beat_cdw) begin
        dc_tc_not_valid_captured       <= 0;
        dc_data_corruption_captured    <= 0;
        dc_misconfig_captured          <= 0;
        pdtv_zero_captured             <= 0;
    end
    else begin
        dc_tc_not_valid_captured       <= dc_tc_not_valid_captured || dc_tc_not_valid;
        dc_data_corruption_captured    <= dc_data_corruption_captured || ready_to_capture_data_corruption;
        dc_misconfig_captured          <= dc_misconfig_captured || ready_to_capture_dc_misconfig;
        pdtv_zero_captured             <= pdtv_zero_captured    || ready_to_capture_pdtv_zero;
    end
end

//////////////////////////////DDTC Cache Modelling/////////////////

rv_iommu::dc_base_t dc_q;
always @(posedge clk_i or negedge rst_ni)
        if(!rst_ni)
            dc_q <= 0;
        else if(dc_tc_active)
            dc_q.tc <= dc_tc_q;
        else if(dc_iohgatp_active)
            dc_q.iohgatp <= dc_iohgatp_q;
        else if(dc_ta_active)
            dc_q.ta <= dc_ta_q;
        else if(dc_fsc_active)
            dc_q.fsc <= dc_fsc_q;
        else
            dc_q <= dc_q;

logic [$clog2(DDTC_ENTRIES) : 0] ddtc_seq_detector [DDTC_ENTRIES - 1 : 0];

logic [DDTC_ENTRIES - 1 : 0] ddtc_hit_n, ddtc_miss_n;
logic ddtc_hit_q, ddtc_miss_q;

logic dc_loaded_with_error, dc_loaded_with_error_captured;
logic dc_pc_with_data_corruption, dc_pc_with_data_corruption_captured;


// didn't included ready_to_capt_valid_type_disalow because dc_loaded_with_error only make sure
// that dc can be store in cache but if ready_to_capt_valid_type_disalow is true, still we can store the dc in ddtc cache
assign dc_loaded_with_error = (ar_did_wider || aw_did_wider) || pdtv_zero_captured || iosatp_invalid || ready_to_capture_ddte_misconfig_rsrv_bits || ready_to_capture_ddt_entry_invalid || ready_to_capture_ddt_data_corruption || dc_tc_not_valid_captured || dc_data_corruption_captured || dc_misconfig_captured;
assign dc_pc_with_data_corruption = ds_resp_i.r.id == 1 && ds_resp_i.r.resp != axi_pkg::RESP_OKAY && ds_resp_i.r_valid;
logic valid_type_disalow_captured, su_visor_not_allowed_captured;

always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni || aw_or_ar_hsk) begin
        dc_loaded_with_error_captured         <= 0;
        dc_pc_with_data_corruption_captured   <= 0;
        valid_type_disalow_captured           <= 0;
        pc_loaded_with_error_captured         <= 0;
        su_visor_not_allowed_captured         <= 0;
    end
    else begin
        dc_loaded_with_error_captured         <= dc_loaded_with_error_captured || dc_loaded_with_error;
        dc_pc_with_data_corruption_captured   <= dc_pc_with_data_corruption_captured || dc_pc_with_data_corruption;
        valid_type_disalow_captured           <= valid_type_disalow_captured || ready_to_capt_valid_type_disalow;
        pc_loaded_with_error_captured         <= pc_loaded_with_error_captured || pc_loaded_with_error;
        su_visor_not_allowed_captured         <= su_visor_not_allowed_captured || su_visor_not_allowed;
    end
end

logic correct_did;
assign correct_did = (dev_tr_req_i.ar_valid || dev_tr_req_i.aw_valid) && (riscv_iommu.ddtp.iommu_mode.q == 4 ||(riscv_iommu.ddtp.iommu_mode.q == 2 && |selected_did[23:6] == 0) || (riscv_iommu.ddtp.iommu_mode.q == 3 && |selected_did[23:15] == 0));


logic req_enable;
assign req_enable = !aw_or_ar_hsk && (dev_tr_req_i.aw_valid || dev_tr_req_i.ar_valid);

logic flush_ddtc;
assign flush_ddtc = !riscv_iommu.flush_pv && ((riscv_iommu.flush_ddtc && !riscv_iommu.flush_dv) || (riscv_iommu.flush_ddtc && riscv_iommu.flush_dv && riscv_iommu.flush_did == selected_did));

logic [DDTC_ENTRIES - 1 : 0] flush_ddtc_miss_n ;

generate
for (genvar i  = 0; i < DDTC_ENTRIES; i++ ) begin

assign flush_ddtc_miss_n[i] = !riscv_iommu.flush_pv && (dev_tr_req_i.aw_valid || dev_tr_req_i.ar_valid) && ((!riscv_iommu.flush_dv && !riscv_iommu.flush_pv) || (riscv_iommu.flush_ddtc && riscv_iommu.flush_dv && riscv_iommu.flush_did == selected_did && selected_did == ddtc_entry[i] && ddtc_entry_valid[i]));
assign ddtc_hit_n[i]  = !flush_ddtc && correct_did && req_enable && ddtc_entry_valid[i] && selected_did == ddtc_entry[i] && !ddtc_miss_q;
assign ddtc_miss_n[i] = !flush_ddtc_miss_q && correct_did && req_enable && (selected_did != ddtc_entry[i] || !ddtc_entry_valid[i]);
end
endgenerate

logic flush_ddtc_miss_q;
always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni || aw_or_ar_hsk)
        flush_ddtc_miss_q  <= 0;
    else
        flush_ddtc_miss_q  <= flush_ddtc_miss_q || flush_ddtc_miss_n != 0;


always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni || aw_or_ar_hsk) begin
        ddtc_hit_q  <= 0;
        ddtc_miss_q <= 0;
    end
    else begin
        ddtc_hit_q  <= ddtc_hit_q  || (ddtc_hit_n != 0);
        ddtc_miss_q <= ddtc_miss_q || ddtc_miss_n == 8'hff;
    end

logic [23:0] ddtc_entry [DDTC_ENTRIES - 1 : 0];
logic ddtc_entry_valid [DDTC_ENTRIES - 1 : 0];
logic ddtc_pdtv [DDTC_ENTRIES - 1 : 0];
logic [3:0] ddtc_fsc_mode [DDTC_ENTRIES - 1 : 0];
logic ddtc_dpe [DDTC_ENTRIES - 1 : 0];
logic [3:0] ddtc_iohgatp_mode [DDTC_ENTRIES - 1 : 0];
logic [15:0] ddtc_gscid [DDTC_ENTRIES - 1 : 0];
logic [19:0] ddtc_pscid [DDTC_ENTRIES - 1 : 0];

always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        for (int i = 0; i < DDTC_ENTRIES; i++ ) begin
            ddtc_entry[i]         <= 0;
            ddtc_entry_valid[i]   <= 0;
            ddtc_seq_detector[i]  <= 0;
            ddtc_pdtv[i]          <= 0;
            ddtc_fsc_mode[i]      <= 0;
            ddtc_dpe[i]           <= 0;
            ddtc_iohgatp_mode[i]  <= 0;
            ddtc_gscid[i]         <= 0;
            ddtc_pscid[i]         <= 0;
        end
/*
If DV is 0, then the inval_ddt invalidates all ddt and PDT entries for all devices
riscv_iommu.flush_pv ---->> This is used to difference between IODIR.INVAL_DDT and IODIR.INVAL_PDT
*/
    else if(riscv_iommu.flush_ddtc && !riscv_iommu.flush_dv && !riscv_iommu.flush_pv) begin
        for (int i = 0; i < DDTC_ENTRIES; i++ ) begin
            ddtc_seq_detector[i]  <= 0;
            ddtc_entry[i]         <= 0;
            ddtc_entry_valid[i]   <= 0;
            ddtc_pdtv[i]          <= 0;
            ddtc_fsc_mode[i]      <= 0;
            ddtc_dpe[i]           <= 0;
            ddtc_iohgatp_mode[i]  <= 0;
            ddtc_gscid[i]         <= 0;
            ddtc_pscid[i]         <= 0;
        end
    end
// If DV is 1, then the inval_ddt invalidates cached leaf-level all associated DDT entries
    else if(riscv_iommu.flush_ddtc && riscv_iommu.flush_dv && !riscv_iommu.flush_pv) begin
        for (int j = 0; j < DDTC_ENTRIES; j++)
            if(ddtc_entry[j] == riscv_iommu.flush_did && ddtc_entry_valid[j]) begin

                for (int i = 0; i < DDTC_ENTRIES; i++ )
                    if(ddtc_seq_detector[j] > ddtc_seq_detector[i])
                        ddtc_seq_detector[i]  <= ddtc_seq_detector[i] - 1;
                ddtc_seq_detector[j]  <= 0;
                ddtc_entry[j]         <= 0;
                ddtc_entry_valid[j]   <= 0;
                ddtc_pdtv[j]          <= 0;
                ddtc_fsc_mode[j]      <= 0;
                ddtc_dpe[j]           <= 0;
                ddtc_iohgatp_mode[j]  <= 0;
                ddtc_gscid[j]         <= 0;
                ddtc_pscid[j]         <= 0;
                break;
            end
    end
    else if(ddtc_miss_q && !dc_loaded_with_error_captured && $rose(dc_ended_captured)) begin
        for (int i = 0; i < DDTC_ENTRIES; i++ ) begin
            if((ddtc_seq_detector[i] == 0 || ddtc_seq_detector[i] == DDTC_ENTRIES)) begin
                ddtc_seq_detector[i]  <= 1;
                ddtc_entry[i]         <= selected_did;
                ddtc_entry_valid[i]   <= 1'b1;
                ddtc_pdtv[i]          <= dc_q.tc.pdtv;
                ddtc_fsc_mode[i]      <= dc_q.fsc.mode;
                ddtc_dpe[i]           <= dc_q.tc.dpe;
                ddtc_iohgatp_mode[i]  <= dc_q.iohgatp.mode;
                ddtc_gscid[i]         <= dc_q.iohgatp.gscid;
                ddtc_pscid[i]         <= dc_q.ta.pscid;
                for (int j = 0; j < DDTC_ENTRIES; j++ )
                    if(!(ddtc_seq_detector[j] == 0 || ddtc_seq_detector[j] == DDTC_ENTRIES))
                        ddtc_seq_detector[j] <= ddtc_seq_detector[j] + 1;

                break;
            end
        end
    end
    else if($rose(ddtc_hit_q)) begin
        for (int i = 0; i < DDTC_ENTRIES; i++ ) begin
            if(ddtc_hit_n[i] == 1 && ddtc_seq_detector[i] != 1) begin
                for (int j = 0; j < DDTC_ENTRIES; j++ ) begin
                    if(ddtc_hit_n[j])
                        ddtc_seq_detector[j] <= 1;
                    else if((ddtc_seq_detector[i] == DDTC_ENTRIES) && ddtc_seq_detector[j] != 0)
                        ddtc_seq_detector[j] <= ddtc_seq_detector[j] - 1;
                    else if(ddtc_seq_detector[j] != 0)
                        ddtc_seq_detector[j] <= ddtc_seq_detector[j] + 1;
                end
                break;
            end
        end
    end
end



/////////////////////////////PDTC Cache modelling///////////////////////////////////
logic [$clog2(PDTC_ENTRIES) : 0] pdtc_seq_detector_n [PDTC_ENTRIES - 1 : 0];
logic [$clog2(PDTC_ENTRIES) : 0] pdtc_seq_detector_sorted [PDTC_ENTRIES - 1 : 0];
logic [$clog2(PDTC_ENTRIES) : 0] pdtc_sff, pdtc_saf, pdtc_temp, pdtc_consec_big;

always_comb begin
    // initialize with 0
    pdtc_sff        = 0;
    pdtc_saf        = 0;
    pdtc_consec_big = 0;
    pdtc_temp       = 0;
    for (int i = 0; i < PDTC_ENTRIES; i++) begin
        pdtc_seq_detector_n[i] = 0;
        pdtc_seq_detector_sorted[i] = 0;
    end
    if(riscv_iommu.flush_ddtc && riscv_iommu.flush_dv && !riscv_iommu.flush_pv) begin
    //    pdtc_sff = pdtc_seq_detector[0];
        for (int i = 0; i < PDTC_ENTRIES; i++) begin
            pdtc_seq_detector_n[i] = pdtc_seq_detector[i];

        // Step 1: Flush wherever requires
            if(pdtc_did[i] == riscv_iommu.flush_did && pdtc_entry_valid[i]) begin
                pdtc_seq_detector_n[i] = 0;

                // Step 2: Take small from flush(sff)
                if(pdtc_sff == 0)
                    pdtc_sff = pdtc_seq_detector[i];
                else if(pdtc_seq_detector[i] < pdtc_sff)
                    pdtc_sff = pdtc_seq_detector[i];
            end

        // Step 3: Sort the sequences after flush
            pdtc_seq_detector_sorted[i] = pdtc_seq_detector_n[i];
        end
        for (int i = 0; i < PDTC_ENTRIES; i++)
            for (int j = 0; j < PDTC_ENTRIES; j++) begin
                 if(pdtc_seq_detector_sorted[i] < pdtc_seq_detector_sorted[j]) begin
                    pdtc_temp = pdtc_seq_detector_sorted[i];
                    pdtc_seq_detector_sorted[i] = pdtc_seq_detector_sorted[j];
                    pdtc_seq_detector_sorted[j] = pdtc_temp;
                end
            end

        // Step 4: Take small after flush(saf)
        // pdtc_saf = pdtc_seq_detector_sorted[0];
        for(int i = 0; i < PDTC_ENTRIES; i++)
          if(pdtc_saf == 0)
            pdtc_saf = pdtc_seq_detector_sorted[i];
          else if(pdtc_seq_detector_sorted[i] < pdtc_saf)
            pdtc_saf = pdtc_seq_detector_sorted[i];

        // Step 5: Take consecutive_big
        pdtc_consec_big = pdtc_sff;
        for(int i = 0; i < PDTC_ENTRIES; i++)
            if(pdtc_seq_detector_sorted[i] == (pdtc_consec_big + 1))
                pdtc_consec_big = pdtc_seq_detector_sorted[i];
    end
    else if(riscv_iommu.flush_pdtc && riscv_iommu.flush_pv) begin
    //    pdtc_sff = pdtc_seq_detector[0];
        for (int i = 0; i < PDTC_ENTRIES; i++) begin
            pdtc_seq_detector_n[i] = pdtc_seq_detector[i];
        // Step 1: Flush wherever requires
            if(pdtc_did[i] == riscv_iommu.flush_did && pdtc_pid[i] == riscv_iommu.flush_pid && pdtc_entry_valid[i]) begin
                pdtc_seq_detector_n[i] = 0;

                // Step 2: Take small from flush(sff)
                if(pdtc_sff == 0)
                    pdtc_sff = pdtc_seq_detector[i];
                else if(pdtc_seq_detector[i] < pdtc_sff)
                    pdtc_sff = pdtc_seq_detector[i];
            end

        // Step 3: Sort the sequences after flush
            pdtc_seq_detector_sorted[i] = pdtc_seq_detector_n[i];
        end

        for (int i = 0; i < PDTC_ENTRIES; i++)
            for (int j = 0; j < PDTC_ENTRIES; j++) begin
                 if(pdtc_seq_detector_sorted[i] < pdtc_seq_detector_sorted[j]) begin
                    pdtc_temp = pdtc_seq_detector_sorted[i];
                    pdtc_seq_detector_sorted[i] = pdtc_seq_detector_sorted[j];
                    pdtc_seq_detector_sorted[j] = pdtc_temp;
                end
            end

        // Step 4: Take small after flush(saf)
        // pdtc_saf = pdtc_seq_detector_sorted[0];
        for(int i = 0; i < PDTC_ENTRIES; i++)
          if(pdtc_saf == 0)
            pdtc_saf = pdtc_seq_detector_sorted[i];
          else if(pdtc_seq_detector_sorted[i] < pdtc_saf)
            pdtc_saf = pdtc_seq_detector_sorted[i];

        // Step 5: Take consecutive_big
        pdtc_consec_big = pdtc_sff;
        for(int i = 0; i < PDTC_ENTRIES; i++)
            if(pdtc_seq_detector_sorted[i] == (pdtc_consec_big + 1))
                pdtc_consec_big = pdtc_seq_detector_sorted[i];
    end

end


logic [$clog2(PDTC_ENTRIES) : 0] pdtc_seq_detector [PDTC_ENTRIES - 1 : 0];
logic [PDTC_ENTRIES - 1 : 0] pdtc_hit_n, pdtc_miss_n;
logic pdtc_hit_q, pdtc_miss_q;

logic correct_pid;
assign correct_pid = (dev_tr_req_i.ar_valid || dev_tr_req_i.aw_valid) && !pid_wider;

logic [PDTC_ENTRIES - 1 : 0] match_pdtc;
logic ddtc_completed, dpe_high;
assign ddtc_completed = (ddtc_hit_q || (ddtc_miss_q && !riscv_iommu.ddt_walk && dc_ended_captured)) && !dc_loaded_with_error_captured;

/* When PDTV is 1, the DPE bit may set to 1 to enable the use of 0 as the default value of process_id for
   translating requests without a valid process_id. */
assign dpe_high       = !selected_pv && ((ddtc_miss_q && dc_q.tc.pdtv && dc_q.tc.dpe) || (ddtc_hit_q && ddtc_pdtv[hit_index] && ddtc_dpe[hit_index]));

generate
for (genvar i  = 0; i < PDTC_ENTRIES; i++ ) begin
assign match_pdtc[i]  = pdtc_entry_valid[i] && selected_did == pdtc_did[i] && ((dpe_high && pdtc_pid[i] == 0) || selected_pid == pdtc_pid[i]);

assign pdtc_hit_n[i]  = (correct_pid || dpe_high) && correct_did && req_enable && match_pdtc[i] && !pdtc_miss_q;
assign pdtc_miss_n[i] = ddtc_completed && !((!selected_pv && !dc_q.tc.dpe) || !dc_q.tc.pdtv || !dc_q.fsc.mode) && (correct_pid || dpe_high) && correct_did && req_enable && !match_pdtc[i];
end
endgenerate

always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni || aw_or_ar_hsk) begin
        pdtc_hit_q  <= 0;
        pdtc_miss_q <= 0;
    end
    else begin
        pdtc_hit_q  <= pdtc_hit_q  || pdtc_hit_n != 0;
        pdtc_miss_q <= pdtc_miss_q || pdtc_miss_n == 8'hff;
    end


logic [19:0] pdtc_pid [PDTC_ENTRIES - 1 : 0];
logic [23:0] pdtc_did [PDTC_ENTRIES - 1 : 0];
logic pdtc_sum [PDTC_ENTRIES - 1 : 0];
logic [3:0] pdtc_fsc_mode [PDTC_ENTRIES - 1 : 0];
logic pdtc_ens [PDTC_ENTRIES - 1 : 0];
logic pdtc_entry_valid [PDTC_ENTRIES - 1 : 0];

always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        for (int i = 0; i < PDTC_ENTRIES; i++ ) begin
            pdtc_pid[i]           <= 0;
            pdtc_did[i]           <= 0;
            pdtc_entry_valid[i]   <= 0;
            pdtc_seq_detector[i]  <= 0;
            pdtc_sum[i]           <= 0;
            pdtc_fsc_mode[i]      <= 0;
            pdtc_ens[i]           <= 0;
        end

// If DV is 0, then the inval_ddt invalidates all ddt and PDT entries for all devices
    else if(riscv_iommu.flush_ddtc && !riscv_iommu.flush_dv && !riscv_iommu.flush_pv) begin
        for (int i = 0; i < PDTC_ENTRIES; i++) begin
            pdtc_seq_detector[i]  <= 0;
            pdtc_did[i]           <= 0;
            pdtc_pid[i]           <= 0;
            pdtc_sum[i]           <= 0;
            pdtc_fsc_mode[i]      <= 0;
            pdtc_entry_valid[i]   <= 0;
            pdtc_ens[i]           <= 0;
        end
    end

// If DV is 1, then the inval_ddt invalidates cached leaf-level all associated PDT entries
    else if(riscv_iommu.flush_ddtc && riscv_iommu.flush_dv && !riscv_iommu.flush_pv) begin
        for(int i = 0; i < PDTC_ENTRIES; i++) begin
            if(pdtc_sff == 1) begin
                if(pdtc_seq_detector_n[i] <= pdtc_consec_big && pdtc_seq_detector_n[i] > pdtc_sff)
                    pdtc_seq_detector[i] <= pdtc_seq_detector_n[i] - 1;
                else if(pdtc_seq_detector_n[i] > pdtc_consec_big && pdtc_seq_detector_n[i] > pdtc_sff)
                    pdtc_seq_detector[i] <= pdtc_seq_detector_n[i] - pdtc_sff;
                else
                    pdtc_seq_detector[i] <= pdtc_seq_detector_n[i];
            end
            else if(pdtc_sff != 0) begin
                if(pdtc_seq_detector_n[i] <= pdtc_consec_big && pdtc_seq_detector_n[i] > pdtc_sff)
                    pdtc_seq_detector[i] <= pdtc_seq_detector_n[i] - 1;
                else if(pdtc_seq_detector_n[i] > pdtc_consec_big && pdtc_seq_detector_n[i] > pdtc_sff)
                    pdtc_seq_detector[i] <= pdtc_seq_detector_n[i] - pdtc_saf;
                else
                    pdtc_seq_detector[i] <= pdtc_seq_detector_n[i];
            end
        end
        for (int j = 0; j < PDTC_ENTRIES; j++)
            if(pdtc_did[j] == riscv_iommu.flush_did && pdtc_entry_valid[j]) begin
                pdtc_did[j]           <= 0;
                pdtc_pid[j]           <= 0;
                pdtc_sum[j]           <= 0;
                pdtc_fsc_mode[j]      <= 0;
                pdtc_entry_valid[j]   <= 0;
                pdtc_ens[j]           <= 0;
            end
    end
    else if(riscv_iommu.flush_pdtc && riscv_iommu.flush_pv) begin
        for(int i = 0; i < PDTC_ENTRIES; i++) begin
            if(pdtc_sff == 1) begin
                if(pdtc_seq_detector_n[i] <= pdtc_consec_big && pdtc_seq_detector_n[i] > pdtc_sff)
                    pdtc_seq_detector[i] <= pdtc_seq_detector_n[i] - 1;
                else if(pdtc_seq_detector_n[i] > pdtc_consec_big && pdtc_seq_detector_n[i] > pdtc_sff)
                    pdtc_seq_detector[i] <= pdtc_seq_detector_n[i] - pdtc_sff;
                else
                    pdtc_seq_detector[i] <= pdtc_seq_detector_n[i];
            end
            else if(pdtc_sff != 0) begin
                if(pdtc_seq_detector_n[i] <= pdtc_consec_big && pdtc_seq_detector_n[i] > pdtc_sff)
                    pdtc_seq_detector[i] <= pdtc_seq_detector_n[i] - 1;
                else if(pdtc_seq_detector_n[i] > pdtc_consec_big && pdtc_seq_detector_n[i] > pdtc_sff)
                    pdtc_seq_detector[i] <= pdtc_seq_detector_n[i] - pdtc_saf;
                else
                    pdtc_seq_detector[i] <= pdtc_seq_detector_n[i];
            end
        end
        for (int j = 0; j < PDTC_ENTRIES; j++)
            if(pdtc_did[j] == riscv_iommu.flush_did && pdtc_pid[j] == riscv_iommu.flush_pid && pdtc_entry_valid[j]) begin
                pdtc_did[j]           <= 0;
                pdtc_pid[j]           <= 0;
                pdtc_sum[j]           <= 0;
                pdtc_fsc_mode[j]      <= 0;
                pdtc_entry_valid[j]   <= 0;
                pdtc_ens[j]           <= 0;
            end
    end
    else if(pdtc_miss_q && counter_pc == 1 && wo_data_corruption && !pc_loaded_with_error_captured && (translation_req.aw_hsk || translation_req.ar_hsk)) begin
        for (int i = 0; i < PDTC_ENTRIES; i++ ) begin
            if((pdtc_seq_detector[i] == 0 || pdtc_seq_detector[i] == PDTC_ENTRIES)) begin
                pdtc_seq_detector[i]  <= 1;
                pdtc_did[i]           <= selected_did;
                pdtc_pid[i]           <= selected_pid;
                pdtc_sum[i]           <= pc_q.ta.sum;
                pdtc_fsc_mode[i]      <= pc_q.fsc.mode;
                pdtc_entry_valid[i]   <= 1'b1;
                pdtc_ens[i]           <= pc_q.ta.ens;
                for (int j = 0; j < PDTC_ENTRIES; j++ )
                    if(!(pdtc_seq_detector[j] == 0 || pdtc_seq_detector[j] == PDTC_ENTRIES))
                        pdtc_seq_detector[j] <= pdtc_seq_detector[j] + 1;

                break;
            end
        end
    end
    else if($rose(pdtc_hit_q)) begin
        for (int i = 0; i < PDTC_ENTRIES; i++ ) begin
            if(pdtc_hit_n[i] == 1 && pdtc_seq_detector[i] != 1) begin
                for (int j = 0; j < PDTC_ENTRIES; j++ ) begin
                    if(pdtc_hit_n[j])
                        pdtc_seq_detector[j] <= 1;
                    else if((pdtc_seq_detector[i] == PDTC_ENTRIES) && pdtc_seq_detector[j] != 0)
                        pdtc_seq_detector[j] <= pdtc_seq_detector[j] - 1;
                    else if(pdtc_seq_detector[j] != 0)
                        pdtc_seq_detector[j] <= pdtc_seq_detector[j] + 1;
                end
                break;
            end
        end
    end
end

//............................IOTLB Started-------------------------------------------------
logic pte_1s_global;

always @(posedge clk_i or negedge rst_ni)
        if(!rst_ni || aw_or_ar_hsk)
            pte_1s_global <= 0;

        else if(trans_1s_in_progress && leaf_pte)
            pte_1s_global <= pte.g;

        else
            pte_1s_global <= pte_1s_global;


logic [$clog2(IOTLB_ENTRIES) : 0] IOTLB_seq_detector [IOTLB_ENTRIES - 1 : 0];

logic [IOTLB_ENTRIES - 1 : 0] IOTLB_hit_n, IOTLB_miss_n;
logic IOTLB_hit_q, IOTLB_miss_q;

logic [IOTLB_ENTRIES - 1 : 0] match_tlb_tag, match_stages, match_gscid, match_pscid, match_addrs_1s, match_addrs_2s;
logic [10:0] vpn2;
logic [8:0] vpn1, vpn0;

assign vpn2 = selected_addr[40:30];
assign vpn1 = selected_addr[29:21];
assign vpn0 = selected_addr[20:12];

logic pc_dc_loaded;
assign pc_dc_loaded = wo_data_corruption && !valid_type_disalow_captured && !su_visor_not_allowed_captured && !ready_to_capt_valid_type_disalow && (!pc_loaded_with_error_captured && (pc_ended_captured || pdtc_hit_q || !pdtv_enable || !InclPC)) && (!dc_loaded_with_error_captured && (ddtc_hit_q || dc_ended_captured));

generate
for (genvar i  = 0; i < IOTLB_ENTRIES; i++ ) begin
assign match_stages[i]   = stage1_enable == IOTLB_en_1s[i] && stage2_enable == IOTLB_en_2s[i];
assign match_gscid[i]    = (stage2_enable && IOTLB_gscid[i] == gscid) || !stage2_enable;
assign match_pscid[i]    = (stage1_enable && (IOTLB_pscid[i] == pscid || IOTLB_pte_global[i])) || !stage1_enable;
assign match_addrs_1s[i] = stage1_enable && (IOTLB_is_1G_1s[i] || (IOTLB_VPN[i][17:9] == vpn1 && (IOTLB_is_2m_1s[i] || IOTLB_VPN[i][8:0] == vpn0)));
assign match_addrs_2s[i] = !stage1_enable && stage2_enable && (IOTLB_is_1G_2s[i] || (IOTLB_VPN[i][17:9] == vpn1 && (IOTLB_is_2m_2s[i] || IOTLB_VPN[i][8:0] == vpn0)));

assign match_tlb_tag[i]  = (match_addrs_1s[i] || match_addrs_2s[i]) && IOTLB_VPN_valid[i] && (stage1_enable ? IOTLB_VPN[i][26:18] == vpn2[8:0] : IOTLB_VPN[i][28:18] == vpn2) && match_stages[i] && match_gscid[i] && match_pscid[i];

assign IOTLB_hit_n[i]   = pc_dc_loaded && !translation_req.aw_hsk && !translation_req.ar_hsk && (dev_tr_req_i.aw_valid || dev_tr_req_i.ar_valid) && match_tlb_tag[i];
assign IOTLB_miss_n[i]  = (stage1_enable || stage2_enable) && pc_dc_loaded && !translation_req.aw_hsk && !translation_req.ar_hsk && (dev_tr_req_i.aw_valid || dev_tr_req_i.ar_valid) && !match_tlb_tag[i];
end
endgenerate


always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
        IOTLB_hit_q  <= 0;
        IOTLB_miss_q <= 0;
    end

    else begin
        if(translation_req.aw_hsk || translation_req.ar_hsk) begin
        IOTLB_hit_q  <= 0;
        IOTLB_miss_q <= 0;
        end
        else begin
        IOTLB_hit_q  <= IOTLB_hit_q  || (IOTLB_hit_n != 0);
        IOTLB_miss_q <= IOTLB_miss_q || IOTLB_miss_n == {IOTLB_ENTRIES{1'b1}};
        end
    end
end

logic [28:0] IOTLB_VPN [IOTLB_ENTRIES - 1 : 0];
logic IOTLB_VPN_valid [IOTLB_ENTRIES - 1 : 0];

logic IOTLB_en_1s [IOTLB_ENTRIES - 1 : 0];
logic IOTLB_en_2s [IOTLB_ENTRIES - 1 : 0];

logic IOTLB_is_2m_1s [IOTLB_ENTRIES - 1 : 0];
logic IOTLB_is_2m_2s [IOTLB_ENTRIES - 1 : 0];

logic IOTLB_is_1G_1s [IOTLB_ENTRIES - 1 : 0];
logic IOTLB_is_1G_2s [IOTLB_ENTRIES - 1 : 0];

logic IOTLB_is_msi [IOTLB_ENTRIES - 1 : 0];

logic [19:0] IOTLB_pscid [IOTLB_ENTRIES - 1 : 0];
logic [15:0] IOTLB_gscid [IOTLB_ENTRIES - 1 : 0];
logic IOTLB_pte_global   [IOTLB_ENTRIES - 1 : 0];

logic [15:0] gscid;
assign gscid = $rose(ddtc_hit_q) ? ddtc_gscid[hit_index] : dc_q.iohgatp.gscid;

logic [19:0] pscid;
assign pscid = $rose(ddtc_hit_q) ? ddtc_pscid[hit_index] : dc_q.ta.pscid;

always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        for (int i = 0; i < IOTLB_ENTRIES; i++ ) begin
            IOTLB_VPN[i]           <= 0;
            IOTLB_VPN_valid[i]     <= 0;
            IOTLB_seq_detector[i]  <= 0;
            IOTLB_pscid[i]         <= 0;
            IOTLB_gscid[i]         <= 0;
            IOTLB_pte_global[i]    <= 0;
            IOTLB_en_1s[i]         <= 0;
            IOTLB_en_2s[i]         <= 0;
            IOTLB_is_2m_2s[i]      <= 0;
            IOTLB_is_2m_1s[i]      <= 0;
            IOTLB_is_1G_1s[i]      <= 0;
            IOTLB_is_1G_2s[i]      <= 0;
            IOTLB_is_msi[i]        <= 0;

        end
    else if(IOTLB_miss_q && !with_error_pte && !with_error_pte_loaded && aw_or_ar_hsk) begin
        for (int i = 0; i < IOTLB_ENTRIES; i++ ) begin
            if((IOTLB_seq_detector[i] == 0 || IOTLB_seq_detector[i] == IOTLB_ENTRIES)) begin
                IOTLB_VPN_valid[i]     <= 1'b1;
                IOTLB_seq_detector[i]  <= 1;
                IOTLB_VPN[i]           <= selected_addr[40:12];
                IOTLB_pscid[i]         <= pscid;
                IOTLB_gscid[i]         <= gscid;
                IOTLB_pte_global[i]    <= pte_1s_global;
                IOTLB_en_1s[i]         <= stage1_enable;
                IOTLB_en_2s[i]         <= stage2_enable;
                IOTLB_is_2m_1s[i]      <= first_s_2M;
                IOTLB_is_2m_2s[i]      <= second_s_2M;
                IOTLB_is_1G_1s[i]      <= first_s_1G;
                IOTLB_is_1G_2s[i]      <= second_s_1G;
                IOTLB_is_msi[i]        <= 0;            //tbd
                for (int j = 0; j < IOTLB_ENTRIES; j++ )
                    if(!(IOTLB_seq_detector[j] == 0 || IOTLB_seq_detector[j] == IOTLB_ENTRIES))
                        IOTLB_seq_detector[j] <= IOTLB_seq_detector[j] + 1;

                break;
            end
        end
    end

    else if($rose(IOTLB_hit_q)) begin

        for (int i = 0; i < DDTC_ENTRIES; i++ ) begin
            if(IOTLB_hit_n[i] == 1 && IOTLB_seq_detector[i] != 1) begin

                for (int j = 0; j < IOTLB_ENTRIES; j++ ) begin
                    if(IOTLB_hit_n[j])
                        IOTLB_seq_detector[j] <= 1;
                    else if((IOTLB_seq_detector[i] == IOTLB_ENTRIES) && IOTLB_seq_detector[j] != 0)
                        IOTLB_seq_detector[j] <= IOTLB_seq_detector[j] - 1;
                    else if(IOTLB_seq_detector[j] != 0)
                        IOTLB_seq_detector[j] <= IOTLB_seq_detector[j] + 1;
                end
                break;
            end
        end
    end
end

logic ready_to_capt_first_s_2M, ready_to_capt_first_s_1G, ready_to_capt_second_s_2M, ready_to_capt_second_s_1G;

assign ready_to_capt_first_s_2M  = trans_1s_in_progress && current_level == 1 && leaf_pte && !first_s_2M;
assign ready_to_capt_first_s_1G  = trans_1s_in_progress && current_level == 2 && leaf_pte && !first_s_1G;
assign ready_to_capt_second_s_2M = trans_2s_in_progress && current_level == 1 && leaf_pte && !second_s_2M;
assign ready_to_capt_second_s_1G = trans_2s_in_progress && current_level == 2 && leaf_pte && !second_s_1G;

logic first_s_2M, first_s_1G, second_s_2M, second_s_1G;
always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni || aw_or_ar_hsk) begin
        first_s_2M  <= 0;
        second_s_2M <= 0;
        first_s_1G  <= 0;
        second_s_1G <= 0;
    end
    else begin
        first_s_2M  <= first_s_2M  || ready_to_capt_first_s_2M;
        second_s_2M <= second_s_2M || ready_to_capt_second_s_2M;
        first_s_1G  <= first_s_1G  || ready_to_capt_first_s_1G;
        second_s_1G <= second_s_1G || ready_to_capt_second_s_1G;
    end
end
// ............................IOTLB Ended-------------------------------------------------

// ----------------------------Process to tranlsate an IOVA checks started----------------------

logic ready_to_capt_valid_type_disalow, valid_pv_pdtv_zero_captured;
assign ready_to_capt_valid_type_disalow = !dc_loaded_with_error && !dc_loaded_with_error_captured && ((selected_pv && ddtc_hit_q && !ddtc_pdtv[hit_index]) || (wo_data_corruption && ds_resp_i.r.id == 1 && ds_resp_i.r_valid && ds_resp_i.r.resp == axi_pkg::RESP_OKAY && (pid_wider || (selected_pv && ((ddtc_miss_q && (dc_ended_captured || ready_to_capt_dc_ended) && !dc_q.tc.pdtv))))));
logic su_visor_not_allowed;
assign su_visor_not_allowed = !ready_to_capt_valid_type_disalow && !dc_loaded_with_error && !dc_loaded_with_error_captured && ((pdtc_hit_q && priv_transac && !pdtc_ens[hit_index]) || (wo_data_corruption && ds_resp_i.r.id == 1 && ds_resp_i.r_valid && ds_resp_i.r.resp == axi_pkg::RESP_OKAY && (pc_ta_active && !pc_ta_q.ens && priv_transac)));

logic pid_wider_when_cache_miss, pid_wider_when_cache_hit;
assign pid_wider_when_cache_miss = ddtc_miss_q && dc_ended_captured && dc_q.tc.pdtv && ((dc_q.fsc.mode == 1 && |selected_pid[19:8]) || ((dc_q.fsc.mode == 2 && |selected_pid[19:17])));
assign pid_wider_when_cache_hit = ddtc_hit_q && ddtc_pdtv[hit_index] && ((ddtc_fsc_mode[hit_index] == 1 && |selected_pid[19:8])  || (ddtc_fsc_mode[hit_index] == 2 && |selected_pid[19:17]));

logic pid_wider;
assign pid_wider = selected_pv && (pid_wider_when_cache_miss || pid_wider_when_cache_hit);

logic [$clog2(DDTC_ENTRIES) : 0] hit_index;
always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        hit_index <= 0;
    else begin
        for (int i  = 0; i < DDTC_ENTRIES; i++ )
            if(ddtc_hit_n[i] == 1) begin
               hit_index <= i;
               break;
            end
    end
end
//---------------------------Process to tranlsate an IOVA checks Ended----------------------



//----------------------------Process directory checks started--------------------------------
rv_iommu::pc_t pc_q;
always @(posedge clk_i or negedge rst_ni)
        if(!rst_ni)
            pc_q <= 0;

        else if(pc_ta_active)
            pc_q.ta <= pc_ta_q;

        else if(pc_fsc_active)
            pc_q.fsc <= pc_fsc_q;

        else
            pc_q <= pc_q;

logic ready_to_capt_dc_ended, dc_ended_captured, ready_to_capt_pc_ended, pc_ended_captured;
assign ready_to_capt_dc_ended = (counter_dc == 3) && data_strcuture.r_hsk_trnsl_compl && last_beat_cdw && !dc_ended_captured;
assign ready_to_capt_pc_ended = pc_fsc_active && data_strcuture.r_hsk_trnsl_compl && !pc_ended_captured && !pc_loaded_with_error && !pc_loaded_with_error_captured;

always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni || aw_or_ar_hsk) begin
        dc_ended_captured <= 0;
        pc_ended_captured <= 0;
    end
    else begin
        dc_ended_captured <= dc_ended_captured || ready_to_capt_dc_ended;
        pc_ended_captured <= pc_ended_captured || ready_to_capt_pc_ended;
    end

logic [1:0] counter_non_leaf_pc;
logic counter_pc;

always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni)
        counter_non_leaf_pc <= 0;

    else if(counter_non_leaf_pc == 1 && ((dc_q.fsc.mode == 2 && ddtc_miss_q) || (ddtc_fsc_mode[hit_index] == 2 && ddtc_hit_q)) && last_beat_cdw && data_strcuture.r_hsk_trnsl_compl) // ddtlevel 2
        counter_non_leaf_pc <= 0;

    else if(counter_non_leaf_pc == 2 && ((dc_q.fsc.mode == 3 && ddtc_miss_q) || (ddtc_fsc_mode[hit_index] == 3 && ddtc_hit_q)) && last_beat_cdw && data_strcuture.r_hsk_trnsl_compl) // ddtlevel 3
        counter_non_leaf_pc <= 0;

    else if(((ddtc_fsc_mode[hit_index] > 1 && ddtc_hit_q) || (dc_ended_captured && dc_q.fsc.mode > 1)) && data_strcuture.r_hsk_trnsl_compl && last_beat_cdw)
        counter_non_leaf_pc <= counter_non_leaf_pc + 1;

logic dc_miss, dc_hit;
assign dc_miss = ddtc_miss_q && (dc_q.fsc.mode == 1 || ((counter_non_leaf_pc == 2 && dc_q.fsc.mode == 3) || (counter_non_leaf_pc == 1 && dc_q.fsc.mode == 2)));
assign dc_hit  = (ddtc_pdtv[hit_index] || ddtc_dpe[hit_index]) && ddtc_hit_q  && (ddtc_fsc_mode[hit_index] == 1 || ((counter_non_leaf_pc == 2 && ddtc_fsc_mode[hit_index] == 3) || (counter_non_leaf_pc == 1 && ddtc_fsc_mode[hit_index] == 2)));

always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni)
        counter_pc <= 0;
    else if(aw_or_ar_hsk)
        counter_pc <= 0;
    else if(counter_pc == 1 && !aw_or_ar_hsk)
        counter_pc <= 1;
    else if((dc_ended_captured || (ddtc_hit_q && ddtc_pdtv[hit_index])) && (dc_hit || dc_miss) && data_strcuture.r_hsk_trnsl_compl && ds_resp_i.r.id == 1)
        counter_pc <= 1;

logic pc_ta_active, pc_fsc_active;

assign pc_ta_active  = (counter_pc == 0 && (dc_hit || (dc_ended_captured && dc_miss))) && ds_resp_i.r.id == 1 && ds_resp_i.r_valid;
assign pc_fsc_active = counter_pc == 1 && ds_resp_i.r.id == 1 && ds_resp_i.r_valid;

rv_iommu::pc_ta_t pc_ta_q;
rv_iommu::fsc_t   pc_fsc_q;

assign pc_ta_q  = pc_ta_active  ? ds_resp_i.r.data : 0;
assign pc_fsc_q = pc_fsc_active ? ds_resp_i.r.data : 0;

logic ready_to_capt_pc_not_valid, pc_not_valid_captured;
assign ready_to_capt_pc_not_valid = pc_ta_active && !pc_ta_q.v && !pc_not_valid_captured;

logic ready_to_capt_pc_misconfig, pc_misconfig_captured;
assign ready_to_capt_pc_misconfig = !pid_wider && !ready_to_capt_pc_not_valid && !pc_not_valid_captured && ((pc_ta_active && (|pc_ta_q.reserved_1 || |pc_ta_q.reserved_2)) || (pc_fsc_active && (!(pc_fsc_q.mode == 0 || pc_fsc_q.mode == 8) || |pc_fsc_q.reserved))) && !pc_misconfig_captured;

logic ready_to_capt_pdte_not_valid, pdte_not_valid_captured;
assign ready_to_capt_pdte_not_valid = !ds_resp_i.r.data[0] && pdte_accessed;

logic ready_to_capt_pdte_misconfig, pdte_misconfig_captured;
assign ready_to_capt_pdte_misconfig = pdte_accessed && !ready_to_capt_pdte_not_valid && (|ds_resp_i.r.data[9:1] || |ds_resp_i.r.data[63:54]);

logic pdte_accessed; // when this is high, pdte is accessed
assign pdte_accessed = dc_ended_captured && ds_resp_i.r.resp == axi_pkg::RESP_OKAY && data_strcuture.r_hsk_trnsl_compl && ds_resp_i.r.id == 1 && !dc_loaded_with_error && counter_pc == 0 && ((dc_q.fsc.mode == 3 && counter_non_leaf_pc < 2) || (!selected_pid[19:17] && dc_q.fsc.mode == 2 && !counter_non_leaf_pc));

always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni) begin
        pdte_misconfig_captured   <= 0;
        pdte_not_valid_captured   <= 0;
    end
    else if(ds_resp_i.r.last && data_strcuture.r_hsk_trnsl_compl && ds_resp_i.r.id == 1) begin
        pdte_misconfig_captured   <= 0;
        pdte_not_valid_captured   <= 0;
    end
    else begin
        pdte_misconfig_captured    <= pdte_misconfig_captured || ready_to_capt_pdte_misconfig;
        pdte_not_valid_captured    <= pdte_not_valid_captured || ready_to_capt_pdte_not_valid;
    end

always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni) begin
        pc_not_valid_captured <= 0;
        pc_misconfig_captured <= 0;
    end
    else if(aw_or_ar_hsk) begin
        pc_not_valid_captured <= 0;
        pc_misconfig_captured <= 0;
    end
    else begin
        pc_not_valid_captured <= pc_not_valid_captured || ready_to_capt_pc_not_valid;
        pc_misconfig_captured <= pc_misconfig_captured || ready_to_capt_pc_misconfig;
    end


logic pc_loaded_with_error, pc_loaded_with_error_captured;
assign pc_loaded_with_error = ready_to_capt_pdte_not_valid || ready_to_capt_pdte_misconfig || ready_to_capt_pc_not_valid || ready_to_capt_pc_misconfig;
//----------------------------Process directory checks Ended--------------------------------


//----------------------------PTW Started-----------------------------------------------
logic pte_active;
assign pte_active = (ds_resp_i.r.id == 0 && ds_resp_i.r_valid);

logic [43:0] pte_1s_ppn, pte_2s_ppn;
always @(posedge clk_i or negedge rst_ni)
    if(!rst_ni || aw_or_ar_hsk) begin
        pte_1s_ppn <= 0;
        pte_2s_ppn <= 0;
    end
    else if(trans_1s_in_progress && leaf_pte)
        pte_1s_ppn <= pte.ppn;
    else if(trans_2s_in_progress && leaf_pte)
        pte_2s_ppn <= pte.ppn;

riscv::pte_t pte;
assign pte = pte_active ? ds_resp_i.r.data : 0;

logic ready_to_capt_pf_excep, pf_excep_captured;
assign ready_to_capt_pf_excep = !ready_to_capt_data_corrup_ptw && pte_active && (!pte.v || (!pte.r && pte.w) || |pte.reserved || (leaf_pte ? !pte.r: (pte.a || pte.d || pte.u)));

logic ready_to_capt_guest_pf_due_to_u_bit, guest_pf_captured_due_to_u_bit;
assign ready_to_capt_guest_pf_due_to_u_bit = !ready_to_capt_data_corrup_ptw && pte_active && (trans_2s_in_progress || trans_iosatp_in_progress || trans_pdtp_in_progress) && !pte.u && (pte.r || pte.x) && !guest_pf_captured_due_to_u_bit;

logic ready_to_capt_guest_pf_due_to_G_bit, guest_pf_captured_due_to_G_bit;
assign ready_to_capt_guest_pf_due_to_G_bit = !ready_to_capt_data_corrup_ptw && pte_active && (trans_2s_in_progress || trans_iosatp_in_progress || trans_pdtp_in_progress) && pte.g && !guest_pf_captured_due_to_G_bit;

logic ready_to_capt_accessed_low, accessed_low_captured;
assign ready_to_capt_accessed_low = !ready_to_capt_misaligned_super_page && pte_active && (pte.r || pte.x) && !ready_to_capt_pf_excep && !ready_to_capt_data_corrup_ptw && !pte.a && !accessed_low_captured;

logic ready_to_capt_dirty_low, dirty_low_captured;
assign ready_to_capt_dirty_low = !ready_to_capt_misaligned_super_page && pte_active && (pte.r || pte.x) && !ready_to_capt_pf_excep && !ready_to_capt_data_corrup_ptw && pte.a && !pte.d && aw_seen_before && !dirty_low_captured;

logic ready_to_capt_data_corrup_ptw, ptw_data_corrup_captured;
assign ready_to_capt_data_corrup_ptw = pte_active && ds_resp_i.r.id == 0 && ds_resp_i.r.resp != axi_pkg::RESP_OKAY && ds_resp_i.r_valid;

logic ready_to_capt_misaligned_super_page;
assign ready_to_capt_misaligned_super_page = (!ready_to_capt_pf_excep && !ready_to_capt_data_corrup_ptw && (pte.r || pte.x)) && (current_level == 2 ? |pte[27 : 10] : (current_level == 1 ? |pte[18 : 10] : 0));

logic guest_pf_63_41_high_39x4;
assign guest_pf_63_41_high_39x4 = (trans_1s_completed && $rose(trans_2s_in_progress || trans_pdtp_in_progress || trans_iosatp_in_progress) && |pte_1s_ppn[43:29]) || (!stage1_enable && stage2_enable && $rose(trans_2s_in_progress) && |selected_addr[63:41]);

always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni) begin
        pf_excep_captured               <= 0;
        ptw_data_corrup_captured        <= 0;
        accessed_low_captured           <= 0;
        dirty_low_captured              <= 0;
        guest_pf_captured_due_to_u_bit  <= 0;
        guest_pf_captured_due_to_G_bit  <= 0;
    end
    else if(aw_or_ar_hsk) begin
        pf_excep_captured               <= 0;
        ptw_data_corrup_captured        <= 0;
        accessed_low_captured           <= 0;
        dirty_low_captured              <= 0;
        guest_pf_captured_due_to_u_bit  <= 0;
        guest_pf_captured_due_to_G_bit  <= 0;
    end
    else begin
        pf_excep_captured              <= pf_excep_captured                 || ready_to_capt_pf_excep;
        ptw_data_corrup_captured       <= ptw_data_corrup_captured          || ready_to_capt_data_corrup_ptw;
        accessed_low_captured          <= accessed_low_captured             || ready_to_capt_accessed_low;
        dirty_low_captured             <= dirty_low_captured                || ready_to_capt_dirty_low;
        guest_pf_captured_due_to_u_bit <= guest_pf_captured_due_to_u_bit    || ready_to_capt_guest_pf_due_to_u_bit;
        guest_pf_captured_due_to_G_bit <= guest_pf_captured_due_to_G_bit    || ready_to_capt_guest_pf_due_to_G_bit;
    end
end

logic with_error_pte, with_error_pte_loaded;
assign with_error_pte = guest_pf_63_41_high_39x4 || ready_to_capt_guest_pf_due_to_u_bit || ready_to_capt_guest_pf_due_to_G_bit || ready_to_capt_misaligned_super_page || ready_to_capt_dirty_low || ready_to_capt_accessed_low || ready_to_capt_data_corrup_ptw || ready_to_capt_pf_excep;

logic [2:0] counter_PTE;

always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        counter_PTE <= 0;
    else if(aw_or_ar_hsk)
        counter_PTE <= 0;
    else if(!with_error_pte && pte_active && (pte.r || pte.x))
        counter_PTE <= counter_PTE + 1;
end

int current_level;
logic decr_crnt_lvl;
assign decr_crnt_lvl = pte_active && !ready_to_capt_pf_excep && !ready_to_capt_data_corrup_ptw && !pte.r && !pte.x && data_strcuture.r_hsk_trnsl_compl;

always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni)
        current_level <= 2;
    else if(aw_or_ar_hsk || (leaf_pte && (trans_iosatp_in_progress || trans_1s_in_progress || trans_2s_in_progress || trans_pdtp_in_progress)))
        current_level <= 2;
    else
        current_level <= current_level - decr_crnt_lvl;
end

logic pdtv_enable, pdtc_stage_1_enable, stage1_enable, stage2_enable;

assign pdtv_enable = (ddtc_miss_q && dc_q.tc.pdtv) || (ddtc_hit_q && ddtc_pdtv[hit_index]);

assign pdtc_stage_1_enable = pdtv_enable && ((pdtc_miss_q && pc_q.fsc.mode != 0) || (pdtc_hit_q && pdtc_fsc_mode[hit_index] != 0));

assign stage1_enable = pdtc_stage_1_enable || (!pdtv_enable && ((ddtc_hit_q && ddtc_fsc_mode[hit_index] != 0) || (ddtc_miss_q && dc_q.fsc.mode != 0)));

assign stage2_enable = (ddtc_miss_q && dc_q.iohgatp.mode != 0) || (ddtc_hit_q && ddtc_iohgatp_mode[hit_index] != 0);

logic user_mode_trans, store_nd_wo_w_permis, x_1_sum_0;
assign user_mode_trans      = !priv_transac && !pte.u && (stage1_enable || stage2_enable);
assign store_nd_wo_w_permis = (stage1_enable || stage2_enable) && pte_active && !pte.w && trans_type == UNTRANSLATED_W;
assign rx_nd_wo_x_permis    = (stage1_enable || stage2_enable) && trans_type == UNTRANSLATED_RX && pte_active && !pte.x;

logic ta_sum_0;
assign ta_sum_0   = pdtc_miss_q ? !pc_q.ta.sum : (pdtc_hit_q && !pdtc_sum[hit_index]);
assign x_1_sum_0  = priv_transac && pte.u && (ta_sum_0 || pte.x);

logic ready_to_capt_s_and_u_mode_fault, s_and_u_mode_fault_captured;
assign ready_to_capt_s_and_u_mode_fault = !ready_to_capt_accessed_low && !ready_to_capt_dirty_low && !ready_to_capt_pf_excep && !ready_to_capt_data_corrup_ptw && !ready_to_capt_misaligned_super_page && (pte.r || pte.x) && pte_active && (rx_nd_wo_x_permis || store_nd_wo_w_permis || user_mode_trans || x_1_sum_0) && !s_and_u_mode_fault_captured;

logic ready_to_capt_super_page;
assign ready_to_capt_super_page = !ready_to_capt_s_and_u_mode_fault && !ready_to_capt_accessed_low && !ready_to_capt_dirty_low && !ready_to_capt_pf_excep && !ready_to_capt_data_corrup_ptw && !ready_to_capt_misaligned_super_page && pte_active && pte.r && current_level > 0 && (pte.r || pte.x);


logic implicit_access;
// will change later pdt_walk with pdt_miss_q...now using internal signal because there is bug in design and also will add condition later when msi is not disabled
assign implicit_access = (ddtc_hit_q && stage2_enable && ddtc_pdtv[hit_index]) || (ddtc_miss_q && stage2_enable && dc_q.tc.pdtv);

logic trans_iosatp_in_progress, iosatp_trans_completed;
assign trans_iosatp_in_progress  = (implicit_access ? counter_PTE == 1 : counter_PTE == 0) && stage1_enable && stage2_enable && pte_active && !iosatp_trans_completed;

logic trans_pdtp_in_progress, pdtp_translated;
assign trans_pdtp_in_progress = implicit_access && counter_PTE == 0 && pte_active && !pdtp_translated;

logic with_second_stage;
assign with_second_stage = (!implicit_access && stage2_enable && iosatp_trans_completed) || (implicit_access && stage2_enable && pdtp_translated && iosatp_trans_completed) || !stage2_enable;

logic trans_1s_in_progress, trans_1s_completed, trans_2s_in_progress, trans_2s_completed;
assign trans_1s_in_progress = stage1_enable && with_second_stage && pte_active && !trans_1s_completed;

assign trans_2s_in_progress = stage2_enable && (stage1_enable ? (trans_1s_completed && (implicit_access ? (iosatp_trans_completed && pdtp_translated) : iosatp_trans_completed)) : ((implicit_access && pdtp_translated) || (!InclPC || !pdtv_enable ))) && pte_active && !trans_2s_completed;

logic ready_to_compl_trans_complete, trans_completed;
assign ready_to_compl_trans_complete = stage2_enable ? (trans_2s_in_progress && leaf_pte) : (stage1_enable && trans_1s_in_progress && leaf_pte) && !trans_completed;

logic leaf_pte;
assign leaf_pte = !ready_to_capt_data_corrup_ptw && (pte.r || pte.x);

always @(posedge clk_i or negedge rst_ni) begin
    if(!rst_ni || aw_or_ar_hsk) begin
        iosatp_trans_completed      <= 0;
        pdtp_translated             <= 0;
        trans_1s_completed          <= 0;
        trans_2s_completed          <= 0;
        with_error_pte_loaded       <= 0;
        trans_completed             <= 0;
        s_and_u_mode_fault_captured <= 0;
    end
    else begin
        iosatp_trans_completed      <= iosatp_trans_completed        || (trans_iosatp_in_progress && leaf_pte);
        pdtp_translated             <= pdtp_translated               || (trans_pdtp_in_progress   && leaf_pte);
        trans_1s_completed          <= trans_1s_completed            || (trans_1s_in_progress     && leaf_pte);
        trans_2s_completed          <= trans_2s_completed            || (trans_2s_in_progress     && leaf_pte);
        trans_completed             <= ready_to_compl_trans_complete || trans_completed;
        with_error_pte_loaded       <= with_error_pte                || with_error_pte_loaded;
        s_and_u_mode_fault_captured <= s_and_u_mode_fault_captured   || ready_to_capt_s_and_u_mode_fault;
    end
end

// address calcultion
logic [55:0] physical_addrs;

always_comb begin
    physical_addrs = 0;

    if(stage1_enable && stage2_enable)
        case ({first_s_2M, first_s_1G, second_s_2M, second_s_1G})

            // 1-S: xx | 2-S: 4k:   {PPN[2], PPN[1],  PPN[0], OFF}
            4'bxx00: physical_addrs = {pte_2s_ppn, selected_addr[11:0]};

            // 1-S: 4k | 2-S: 1G:   {PPN[2], GPPN[1],  GPPN[0], OFF}
            4'b0001: physical_addrs = {pte_2s_ppn[43:18], pte_1s_ppn[17:0], selected_addr[11:0]};

            // 1-S: 4k | 2-S: 1M:   {PPN[2], PPN[1],  GPPN[0], OFF}
            4'b0010: physical_addrs = {pte_2s_ppn[43:9], pte_1s_ppn[8:0], selected_addr[11:0]};

            // 1-S: 1G | 2-S: 1G:    {PPN[2], VPN[1],  VPN[0],  OFF}
            4'b0101: physical_addrs = {pte_2s_ppn[43:18],selected_addr[29:0]};

            // 1-S: 1G | 2-S: 1G:    {PPN[2], GPPN[1], VPN[0],  OFF}
            4'b1001: physical_addrs = {pte_2s_ppn[43:18], pte_1s_ppn[17:9], selected_addr[20:0]};

            // 1-S: 2M | 2-S: 2M:   {PPN[2], PPN[1],  VPN[0],  OFF}
            // 1-S: 1G | 2-S: 2M:   {PPN[2], PPN[1],  VPN[0],  OFF}
            4'b0110, 4'b1010: physical_addrs = {pte_2s_ppn[43:9], selected_addr[20:0]};

            default:;
        endcase

    else if(stage1_enable && !stage2_enable)
        case ({first_s_2M, first_s_1G})

            // 1-S: 4k  | 2-S: disable : {PPN[2], PPN[1],  PPN[0], OFF}
            2'b00: physical_addrs = {pte_1s_ppn, selected_addr[11:0]};

            // 1-S: 1G  | 2-S: disable : {PPN[2], PPN[1],  VPN[0], OFF}
            2'b01: physical_addrs = {pte_1s_ppn[43:18], selected_addr[29:0]};

            // 1-S: 1M  | 2-S: disable : {PPN[2], PPN[1],  VPN[0], OFF}
            2'b10: physical_addrs = {pte_1s_ppn[43:9], selected_addr[20:0]};

            default:;
        endcase

    else if(!stage1_enable && stage2_enable)
        case ({second_s_2M, second_s_1G})

            // 1-S: disable  | 2-S: 4k : {PPN[2], PPN[1], PPN[0], OFF}
            2'b00: physical_addrs = {pte_2s_ppn, selected_addr[11:0]};

            // 1-S: disable  | 2-S: 1G : {PPN[2], VPN[1], VPN[0], OFF}
            2'b01: physical_addrs = {pte_2s_ppn[43:18], selected_addr[29:0]};

            // 1-S: disable  | 2-S: 1M : {PPN[2], PPN[1], VPN[0], OFF}
            2'b10: physical_addrs = {pte_2s_ppn[43:9], selected_addr[20:0]};

            default:;
        endcase

end

logic compare_addr;
assign compare_addr = !s_and_u_mode_fault_captured && trans_completed && (stage1_enable || stage2_enable) && !with_error_pte && !with_error_pte_loaded;

assrt_63_addr:
assert property (compare_addr |-> riscv_iommu.spaddr == physical_addrs);
//----------------------------PTW Ended-----------------------------------------------



//----------------------------- Assertion Started----------------------------------------

// if ddte.v = 0, then cause must be DDT_ENTRY_INVALID
assrt_1_ddt_entry_invalid_error: assert property (ddt_entry_invalid_captured && last_beat_cdw |=> $past(riscv_iommu.trans_error) || riscv_iommu.trans_error);

// if ddte.v = 0, then cause must be DDT_ENTRY_INVALID
assrt_2_ddt_entry_invalid_cause_code: assert property (ddt_entry_invalid_captured && last_beat_cdw |=> $past(riscv_iommu.cause_code) == rv_iommu::DDT_ENTRY_INVALID || riscv_iommu.cause_code == rv_iommu::DDT_ENTRY_INVALID );

// if resp!=ok then cause must be ddt_data_corruption
assrt_3_ddt_data_corruption: assert property (ddt_data_corruption_captured && last_beat_cdw |-> riscv_iommu.trans_error && riscv_iommu.cause_code == rv_iommu::DDT_DATA_CORRUPTION);

// if reserved bits of ddte are set high then cause must be ddt_entry_misconfigured
assrt_4_ddt_misconfigured_non_leaf: assert property (ready_to_capture_ddte_misconfig_rsrv_bits && last_beat_cdw |=> riscv_iommu.trans_error && riscv_iommu.cause_code == rv_iommu::DDT_ENTRY_MISCONFIGURED);

// if did length higher bits are set to 1 then cause must be TRANS_TYPE_DISALLOWED
assrt_5_did_length_wider: assume property (ar_did_wider || aw_did_wider |-> riscv_iommu.trans_error && riscv_iommu.cause_code == rv_iommu::TRANS_TYPE_DISALLOWED);

// if mode is bare then cause must be ALL_INB_TRANSACTION_DISALLOWED
assrt_6_ddtp_mode_off: assume property (riscv_iommu.ddtp.iommu_mode.q == 0 && aw_or_ar_hsk |-> riscv_iommu.trans_error && riscv_iommu.cause_code == rv_iommu::ALL_INB_TRANSACTIONS_DISALLOWED );

generate
for (genvar i = 0; i < riscv::PLEN; i++) begin
// if mode is bare, then the input address is equal to the physical address
assrt_7_ddtp_mode_1_ar: assume property (riscv_iommu.ddtp.iommu_mode.q == 1 && translation_req.ar_hsk |-> `ar_addr[i] == riscv_iommu.spaddr[i]);

// if mode is bare, then the input address is equal to the physical address
assrt_8_ddtp_mode_1_aw: assume property (riscv_iommu.ddtp.iommu_mode.q == 1 && translation_req.aw_hsk |-> `aw_addr[i] == riscv_iommu.spaddr[i]);
end
endgenerate

// if axi resp!=Ok then cause must be DDT_DATA_CORRUPTION
assrt_9_ddt_data_corruption: assert property (dc_data_corruption_captured && last_beat_cdw |->  riscv_iommu.cause_code == rv_iommu::DDT_DATA_CORRUPTION);

// if axi resp==Ok and tc.V==0 then cause must be DDT_ENTRY_INVALID
assrt_10_dc_tc_not_valid: assert property (wo_data_corruption && dc_tc_not_valid_captured && last_beat_cdw |-> riscv_iommu.cause_code == rv_iommu::DDT_ENTRY_INVALID);

// if axi resp==Ok, tc.V==1 and misconfig checks are captured then cause must be DDT_ENTRY_MISCONFIGURED
assrt_11_dc_misconfig: assert property (wo_data_corruption && dc_misconfig_captured && last_beat_cdw |=> ($past(riscv_iommu.cause_code) == rv_iommu::DDT_ENTRY_MISCONFIGURED) || (riscv_iommu.cause_code == rv_iommu::DDT_ENTRY_MISCONFIGURED));

assrt_12_dc_misconfig_pc: assert property (iosatp_invalid |=> riscv_iommu.cause_code == rv_iommu::DDT_ENTRY_MISCONFIGURED );

logic not_ddte;
assign not_ddte = ddtp.iommu_mode.q == 2 || ((counter_non_leaf == 2 && ddtp.iommu_mode.q == 4) || (counter_non_leaf == 1 && ddtp.iommu_mode.q == 3));

assrt_13_2_dc_misconfig_pc: assert property (iosatp_invalid |=> $past(riscv_iommu.trans_error) || riscv_iommu.trans_error);
assrt_14_dc_misconfig_wo_pc: assert property (riscv_iommu.cause_code == rv_iommu::DDT_ENTRY_MISCONFIGURED && $past(not_ddte) |=> iosatp_invalid || ((dc_misconfig_captured || ready_to_capture_ddte_misconfig_rsrv_bits) && last_beat_cdw));

assrt_15_ddt_walk: // if data is not present, there will be ddt_walk
assert property ($rose(ddtc_miss_q) |=> riscv_iommu.ddt_walk);

// if data is not present in the cache then there must be ddt_walk
assrt_16_ddt_walk: assert property (riscv_iommu.ddt_walk |-> $past(ddtc_miss_q));

// if data is present then there will be no ddt_walk
assrt_17_ddt_walk_off: assert property ($rose(ddtc_hit_q) |=> !riscv_iommu.ddt_walk);

logic wo_data_corruption;
assign wo_data_corruption = !dc_pc_with_data_corruption_captured && !dc_pc_with_data_corruption;

// if did length higher bits are set to 1 then cause must be TRANS_TYPE_DISALLOWED
if(!InclPC)
assrt_18_pdtv_zero: assert property (wo_data_corruption && pdtv_zero_captured && last_beat_cdw |-> riscv_iommu.trans_error && riscv_iommu.cause_code == rv_iommu::TRANS_TYPE_DISALLOWED);

// error and valid can't be true at the same time
assrt_19_error_and_valid_both_high: assert property (!(riscv_iommu.trans_error && riscv_iommu.trans_valid));

assrt_20_type_disallow_error: assert property (ready_to_capt_valid_type_disalow && last_beat_cdw |-> riscv_iommu.trans_error);

assrt_21_type_disallow_error: assert property (ready_to_capt_valid_type_disalow && last_beat_cdw |-> riscv_iommu.cause_code == rv_iommu::TRANS_TYPE_DISALLOWED);

// if data is not present, there will be pdt_walk
assrt_22_pdt_walk: assert property ($rose(pdtc_miss_q) |-> riscv_iommu.pdt_walk);
assrt_23_pdt_walk: assert property (riscv_iommu.pdt_walk |-> (pdtc_miss_q));

// if data is present, there will be no pdt_walk
assrt_24_pdt_walk_off: assert property ($rose(pdtc_hit_q) |=> !riscv_iommu.pdt_walk);

// if pdte.v == 0 then cause code must be PDT_ENTRY_INVALID
assrt_25_pdte_not_valid: assert property (ready_to_capt_pdte_not_valid |=> riscv_iommu.trans_error && riscv_iommu.cause_code == rv_iommu::PDT_ENTRY_INVALID);

// if there are misconfiguration while doing directory walk then cause code must be PDT_ENTRY_MISCONFIGURED
assrt_26_pdte_misconfig: assert property (ready_to_capt_pdte_misconfig |=> riscv_iommu.trans_error && riscv_iommu.cause_code == rv_iommu::PDT_ENTRY_MISCONFIGURED);

// if pc.ta.v==0 then cause code must be PDT_ENTRY_INVALID
assrt_27_pc_not_valid: assert property (pc_not_valid_captured && wo_data_corruption && last_beat_cdw |-> riscv_iommu.trans_error && riscv_iommu.cause_code == rv_iommu::PDT_ENTRY_INVALID);

// if there are misconfiguration in pc then cause code must be PDT_ENTRY_MISCONFIGURED
assrt_28_pc_misconfig: assert property (pc_misconfig_captured && wo_data_corruption && last_beat_cdw |-> riscv_iommu.trans_error && riscv_iommu.cause_code == rv_iommu::PDT_ENTRY_MISCONFIGURED);

assrt_29_ptw_pg_fault_trans_error: assert property ($rose(pf_excep_captured) |-> riscv_iommu.trans_error);

assrt_30_ptw_corrupt: assert property ($rose(ptw_data_corrup_captured) |-> riscv_iommu.cause_code == rv_iommu::PT_DATA_CORRUPTION);

assrt_31_ptw_corrupt_trans_error:assert property ($rose(ptw_data_corrup_captured) |-> riscv_iommu.trans_error);

// if pte.a == 0 then there must be error
assrt_32_ptw_accessed_bit: assert property ($rose(accessed_low_captured) |-> riscv_iommu.trans_error);

// if pte.a == 0 then cause code must be store/load page fault
assrt_33_ptw_accessed_bit: assert property ($rose(accessed_low_captured) |-> riscv_iommu.cause_code == rv_iommu::STORE_PAGE_FAULT || riscv_iommu.cause_code == rv_iommu::LOAD_PAGE_FAULT);

// if pte.d == 0 then there must be error cause code must be store page fault
assrt_34_ptw_dirty_bit: assert property ($rose(dirty_low_captured) |-> riscv_iommu.trans_error);
assrt_35_ptw_dirty_bit: assert property ($rose(dirty_low_captured) |-> riscv_iommu.cause_code == rv_iommu::STORE_PAGE_FAULT);

// if ptw perform more than 3 levels then there must be error
assrt_36_level_less_than_0_error: assert property (current_level < 0 && $changed(current_level) |-> riscv_iommu.trans_error);
assrt_37_level_less_than_0_cause_code: assert property (current_level < 0 && aw_seen_before && $changed(current_level) |-> riscv_iommu.cause_code == rv_iommu::STORE_PAGE_FAULT);
assrt_38_level_less_than_0_cause_code: assert property (current_level < 0 && !aw_seen_before && $changed(current_level) |-> riscv_iommu.cause_code == rv_iommu::LOAD_PAGE_FAULT);

assrt_39_misaligned_error: assert property (ready_to_capt_misaligned_super_page |=> riscv_iommu.trans_error);

assrt_40_misaligned_cause_code: assert property (ready_to_capt_misaligned_super_page && aw_seen_before |=> riscv_iommu.cause_code == rv_iommu::STORE_PAGE_FAULT);

assrt_41_misaligned_cause_code: assert property (ready_to_capt_misaligned_super_page && !aw_seen_before |=> riscv_iommu.cause_code == rv_iommu::LOAD_PAGE_FAULT);

assrt_42_data_corruption_error: assert property (ready_to_capt_data_corrup_ptw |=> riscv_iommu.trans_error);

assrt_43_data_corruption_cause_code: assert property (ready_to_capt_data_corrup_ptw |=> riscv_iommu.cause_code == rv_iommu::PT_DATA_CORRUPTION);

assrt_44_super_page_valid: assert property (ready_to_capt_super_page && ready_to_compl_trans_complete |=> riscv_iommu.trans_valid);

assrt_45_super_page: assert property (ready_to_capt_super_page && ready_to_compl_trans_complete |=> riscv_iommu.is_superpage);

assrt_46_sum_o_error: assert property (ready_to_capt_s_and_u_mode_fault |=> riscv_iommu.trans_error);

assrt_47_sum_o_cause_code: assert property (ready_to_capt_s_and_u_mode_fault && !aw_seen_before |=> riscv_iommu.cause_code == rv_iommu::LOAD_PAGE_FAULT);

assrt_48_sum_o_cause_code: assert property (ready_to_capt_s_and_u_mode_fault && aw_seen_before |=> riscv_iommu.cause_code == rv_iommu::STORE_PAGE_FAULT);

assrt_49_su_visor_error: assert property (su_visor_not_allowed && last_beat_cdw |-> riscv_iommu.trans_error);

assrt_50_su_visor_cause_code: assert property (su_visor_not_allowed && last_beat_cdw |-> riscv_iommu.cause_code == rv_iommu::TRANS_TYPE_DISALLOWED);

assrt_51_guest_pf_exception: assert property ($rose(guest_pf_captured_due_to_u_bit) |-> riscv_iommu.trans_error);

assrt_52_guest_pf_exception_due_to_u_cause_code_1: assert property ($rose(guest_pf_captured_due_to_u_bit) && aw_seen_before |-> riscv_iommu.cause_code == rv_iommu::STORE_GUEST_PAGE_FAULT);

assrt_53_guest_pf_exception_due_to_u_cause_code_2: assert property ($rose(guest_pf_captured_due_to_u_bit) && !aw_seen_before |-> riscv_iommu.cause_code == rv_iommu::LOAD_GUEST_PAGE_FAULT);

assrt_54_guest_pf_exception_due_to_g_bit: assert property ($rose(guest_pf_captured_due_to_G_bit) |-> riscv_iommu.trans_error);

assrt_55_guest_pf_exception_due_to_g_cause_code_1: assert property ($rose(guest_pf_captured_due_to_G_bit) && aw_seen_before |-> riscv_iommu.cause_code == rv_iommu::STORE_GUEST_PAGE_FAULT);

assrt_56_guest_pf_exception_due_to_g_cause_code_2: assert property ($rose(guest_pf_captured_due_to_G_bit) && !aw_seen_before |-> riscv_iommu.cause_code == rv_iommu::LOAD_GUEST_PAGE_FAULT);

// if data is not present in the IOTLB, there will be ptw
assrt_57_ptw_walk: assert property ($rose(IOTLB_miss_q) |=> riscv_iommu.s1_ptw || riscv_iommu.s2_ptw);

// if data is not present, there will be iotlb miss
assrt_58_iotlb_miss: assert property ($rose(IOTLB_miss_q) |-> riscv_iommu.iotlb_miss);

// if data is present, there will be no iotlb miss
assrt_59_iotlb_hit: assert property ($rose(IOTLB_hit_q) |-> !riscv_iommu.iotlb_miss);

// if data is not present, there will be no page table walk
assrt_60_ptw_walk: assert property ($rose(IOTLB_hit_q) |=> !(riscv_iommu.s1_ptw || riscv_iommu.s2_ptw));

// for sv39*4 63:41 must all be 0
assrt_61_high_63_41_error: assert property (guest_pf_63_41_high_39x4 |=> riscv_iommu.trans_error);

// for sv39*4 63:41 must all be 0
assrt_62_high_63_41_causecode: assert property (guest_pf_63_41_high_39x4 |=> aw_seen_before ? riscv_iommu.cause_code == rv_iommu::STORE_GUEST_PAGE_FAULT : riscv_iommu.cause_code == rv_iommu::LOAD_GUEST_PAGE_FAULT);

//-----------------------------Covers Started---------------------------------------------

cov_1_checking_dc:
cover property (counter_dc == 2 && riscv_iommu.ddtp.iommu_mode.q == 4);

cov_2_cause_code_define:
cover property (riscv_iommu.cause_code == 263 && riscv_iommu.i_rv_iommu_translation_wrapper.wrap_cause_code == 260);

cov_3_dc_valid:
cover property (dc_tc_not_valid_captured && last_beat_cdw |-> riscv_iommu.cause_code == rv_iommu::DDT_ENTRY_INVALID);

cov_4_dc_misconfig:
cover property (dc_misconfig_captured && last_beat_cdw);

cov_5_error:
cover property (riscv_iommu.trans_error && riscv_iommu.cause_code != 260 ##[1:$] !dc_loaded_with_error && correct_did && riscv_iommu.cause_code == 260 );

cov_6_checking_cache:
cover property ($rose(ddtc_hit_q) ##[0:$] $rose(ddtc_miss_q));

cov_7_update_not_existing:
cover property (($rose(ddtc_miss_q) ##5 !ddtc_miss_q)[*8]);

cov_8_seq_det_4:
cover property (ddtc_seq_detector[4] == 1);

cov_9_seq_det_7:
cover property (ddtc_seq_detector[7] == 1);

// cover_10_unique:
// cover property ($onehot0(ddtc_hit_n));

cover_11_ptw_checker:
cover property (ds_resp_i.r.id == 0 && ds_resp_i.r_valid);

cover_12_error_and_valid_both_high:
cover property (counter_dc != 0 && translation_compl.ar_hsk_trnsl_compl && riscv_iommu.trans_valid);

cover_13_unique_case:
cover property (i_rv_iommu_translation_wrapper.gen_pc_support.i_rv_iommu_tw_sv39x4_pc.wrap_error && i_rv_iommu_translation_wrapper.gen_pc_support.i_rv_iommu_tw_sv39x4_pc.ptw_error);

cover_14_both_stages:
cover property (selected_pv && stage1_enable && stage2_enable && riscv_iommu.trans_valid);

cover_15_both_stages_wo_pc:
cover property (stage1_enable && stage2_enable && riscv_iommu.trans_valid);

cover_16_tlb_hit:
cover property (stage1_enable && stage2_enable && i_rv_iommu_translation_wrapper.gen_pc_support.i_rv_iommu_tw_sv39x4_pc.i_rv_iommu_iotlb_sv39x4.lu_hit_o);

cover_17_pdtc_cache_seq_check:
cover property (pdtc_seq_detector[0] == 1 && pdtc_seq_detector[1] == 2 && riscv_iommu.flush_ddtc && riscv_iommu.flush_dv && !riscv_iommu.flush_pv |=> pdtc_seq_detector[1] == 1 && pdtc_entry_valid[1]);

cover_18_pdtc_cache_seq_check:
cover property (pdtc_seq_detector[0] == 1 && pdtc_seq_detector[1] == 2 && riscv_iommu.flush_ddtc && riscv_iommu.flush_dv && !riscv_iommu.flush_pv);
