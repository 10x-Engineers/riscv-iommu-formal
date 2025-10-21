// Copyright © 2025 Muhammad Hayat, 10xEngineers.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and limitations under the License.

bind riscv_iommu iommu_sva #(
                                .IOTLB_ENTRIES(IOTLB_ENTRIES),
                                .DDTC_ENTRIES(DDTC_ENTRIES),
                                .PDTC_ENTRIES(PDTC_ENTRIES),
                                .MRIFC_ENTRIES(MRIFC_ENTRIES),
                                .MSITrans(MSITrans),
				.IGS(IGS),
                                .InclPC(InclPC),
                                .N_INT_VEC(N_INT_VEC),
                                .N_IOHPMCTR(N_IOHPMCTR),
                                .ADDR_WIDTH(ADDR_WIDTH),
                                .DATA_WIDTH(DATA_WIDTH),
                                .ID_WIDTH(ID_WIDTH),
                                .ID_SLV_WIDTH(ID_SLV_WIDTH),
                                .USER_WIDTH(USER_WIDTH),
                                .aw_chan_t(aw_chan_t),
                                .w_chan_t(w_chan_t),
                                .b_chan_t(b_chan_t),
                                .ar_chan_t(ar_chan_t),
                                .r_chan_t(r_chan_t),
                                .axi_req_t(axi_req_t),
                                .axi_rsp_t(axi_rsp_t),
                                .axi_req_slv_t(axi_req_slv_t),
                                .axi_rsp_slv_t(axi_rsp_slv_t),
                                .axi_req_iommu_t(axi_req_iommu_t),
                                .reg_req_t(reg_req_t),
                                .reg_rsp_t(reg_rsp_t)
                                )
                                sva(.*);
