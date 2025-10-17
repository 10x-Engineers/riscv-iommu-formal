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