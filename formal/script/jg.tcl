# Copyright © 2025 Muhammad Hayat, 10xEngineers.

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# http://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and limitations under the License.

global env
clear -all

set lab_path          $env(FPV_PATH)
set design_top        $env(DUT_TOP)

analyze -sv09 -f $lab_path/script/files.f

analyze -sv09 $lab_path/bind/iommu_bind.sv \
                        $lab_path/sva/iommu_sva.sv

elaborate  -top $design_top -disable_auto_bbox -create_related_covers {precondition witness}

clock clk_i
reset ~rst_ni

get_design_info

set_engine_mode auto

set_proofgrid_manager on

stopat  {dbg_if_ctl ddtp.iommu_mode.q fctl flush_*}

# set_visualize_preload_signal_list /home/hayat/riscv-iommu/formal/waveform/tr_logic_wrapper.sig

##set_visualize_show_default_signals off
prove -bg -all
