module

public import ASDExplicitGamma.Native.HeatOldStepCertificates

/-! Exact radical checks along the OLD producer path. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

-- Elaborate these kernel checks one at a time: with asynchronous elaboration the checks are held together
-- until the end of the file and peak at ~9 GiB; sequentially they peak at ~2 GiB for the same CPU time.
set_option Elab.async false

theorem heat_old_steps_089_valid :
    0 ≤ nativeGap089Raw.1 ∧ 0 ≤ nativeGap089Raw.2.1 ∧ 0 ≤ nativeGap089Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap089Raw.1
      (heatOldIncrement 89 nativeGap089Raw.1 nativeGap089Raw.2.1 nativeGap089Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_090_valid :
    0 ≤ nativeGap090Raw.1 ∧ 0 ≤ nativeGap090Raw.2.1 ∧ 0 ≤ nativeGap090Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap090Raw.1
      (heatOldIncrement 90 nativeGap090Raw.1 nativeGap090Raw.2.1 nativeGap090Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_091_valid :
    0 ≤ nativeGap091Raw.1 ∧ 0 ≤ nativeGap091Raw.2.1 ∧ 0 ≤ nativeGap091Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap091Raw.1
      (heatOldIncrement 91 nativeGap091Raw.1 nativeGap091Raw.2.1 nativeGap091Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_092_valid :
    0 ≤ nativeGap092Raw.1 ∧ 0 ≤ nativeGap092Raw.2.1 ∧ 0 ≤ nativeGap092Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap092Raw.1
      (heatOldIncrement 92 nativeGap092Raw.1 nativeGap092Raw.2.1 nativeGap092Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_093_valid :
    0 ≤ nativeGap093Raw.1 ∧ 0 ≤ nativeGap093Raw.2.1 ∧ 0 ≤ nativeGap093Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap093Raw.1
      (heatOldIncrement 93 nativeGap093Raw.1 nativeGap093Raw.2.1 nativeGap093Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_094_valid :
    0 ≤ nativeGap094Raw.1 ∧ 0 ≤ nativeGap094Raw.2.1 ∧ 0 ≤ nativeGap094Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap094Raw.1
      (heatOldIncrement 94 nativeGap094Raw.1 nativeGap094Raw.2.1 nativeGap094Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_095_valid :
    0 ≤ nativeGap095Raw.1 ∧ 0 ≤ nativeGap095Raw.2.1 ∧ 0 ≤ nativeGap095Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap095Raw.1
      (heatOldIncrement 95 nativeGap095Raw.1 nativeGap095Raw.2.1 nativeGap095Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_096_valid :
    0 ≤ nativeGap096Raw.1 ∧ 0 ≤ nativeGap096Raw.2.1 ∧ 0 ≤ nativeGap096Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap096Raw.1
      (heatOldIncrement 96 nativeGap096Raw.1 nativeGap096Raw.2.1 nativeGap096Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_097_valid :
    0 ≤ nativeGap097Raw.1 ∧ 0 ≤ nativeGap097Raw.2.1 ∧ 0 ≤ nativeGap097Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap097Raw.1
      (heatOldIncrement 97 nativeGap097Raw.1 nativeGap097Raw.2.1 nativeGap097Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_098_valid :
    0 ≤ nativeGap098Raw.1 ∧ 0 ≤ nativeGap098Raw.2.1 ∧ 0 ≤ nativeGap098Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap098Raw.1
      (heatOldIncrement 98 nativeGap098Raw.1 nativeGap098Raw.2.1 nativeGap098Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_099_valid :
    0 ≤ nativeGap099Raw.1 ∧ 0 ≤ nativeGap099Raw.2.1 ∧ 0 ≤ nativeGap099Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap099Raw.1
      (heatOldIncrement 99 nativeGap099Raw.1 nativeGap099Raw.2.1 nativeGap099Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_100_valid :
    0 ≤ nativeGap100Raw.1 ∧ 0 ≤ nativeGap100Raw.2.1 ∧ 0 ≤ nativeGap100Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap100Raw.1
      (heatOldIncrement 100 nativeGap100Raw.1 nativeGap100Raw.2.1 nativeGap100Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_101_valid :
    0 ≤ nativeGap101Raw.1 ∧ 0 ≤ nativeGap101Raw.2.1 ∧ 0 ≤ nativeGap101Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap101Raw.1
      (heatOldIncrement 101 nativeGap101Raw.1 nativeGap101Raw.2.1 nativeGap101Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_102_valid :
    0 ≤ nativeGap102Raw.1 ∧ 0 ≤ nativeGap102Raw.2.1 ∧ 0 ≤ nativeGap102Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap102Raw.1
      (heatOldIncrement 102 nativeGap102Raw.1 nativeGap102Raw.2.1 nativeGap102Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_103_valid :
    0 ≤ nativeGap103Raw.1 ∧ 0 ≤ nativeGap103Raw.2.1 ∧ 0 ≤ nativeGap103Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap103Raw.1
      (heatOldIncrement 103 nativeGap103Raw.1 nativeGap103Raw.2.1 nativeGap103Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_104_valid :
    0 ≤ nativeGap104Raw.1 ∧ 0 ≤ nativeGap104Raw.2.1 ∧ 0 ≤ nativeGap104Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap104Raw.1
      (heatOldIncrement 104 nativeGap104Raw.1 nativeGap104Raw.2.1 nativeGap104Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_105_valid :
    0 ≤ nativeGap105Raw.1 ∧ 0 ≤ nativeGap105Raw.2.1 ∧ 0 ≤ nativeGap105Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap105Raw.1
      (heatOldIncrement 105 nativeGap105Raw.1 nativeGap105Raw.2.1 nativeGap105Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_106_valid :
    0 ≤ nativeGap106Raw.1 ∧ 0 ≤ nativeGap106Raw.2.1 ∧ 0 ≤ nativeGap106Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap106Raw.1
      (heatOldIncrement 106 nativeGap106Raw.1 nativeGap106Raw.2.1 nativeGap106Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_107_valid :
    0 ≤ nativeGap107Raw.1 ∧ 0 ≤ nativeGap107Raw.2.1 ∧ 0 ≤ nativeGap107Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap107Raw.1
      (heatOldIncrement 107 nativeGap107Raw.1 nativeGap107Raw.2.1 nativeGap107Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_108_valid :
    0 ≤ nativeGap108Raw.1 ∧ 0 ≤ nativeGap108Raw.2.1 ∧ 0 ≤ nativeGap108Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap108Raw.1
      (heatOldIncrement 108 nativeGap108Raw.1 nativeGap108Raw.2.1 nativeGap108Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_109_valid :
    0 ≤ nativeGap109Raw.1 ∧ 0 ≤ nativeGap109Raw.2.1 ∧ 0 ≤ nativeGap109Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap109Raw.1
      (heatOldIncrement 109 nativeGap109Raw.1 nativeGap109Raw.2.1 nativeGap109Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_110_valid :
    0 ≤ nativeGap110Raw.1 ∧ 0 ≤ nativeGap110Raw.2.1 ∧ 0 ≤ nativeGap110Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap110Raw.1
      (heatOldIncrement 110 nativeGap110Raw.1 nativeGap110Raw.2.1 nativeGap110Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_111_valid :
    0 ≤ nativeGap111Raw.1 ∧ 0 ≤ nativeGap111Raw.2.1 ∧ 0 ≤ nativeGap111Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap111Raw.1
      (heatOldIncrement 111 nativeGap111Raw.1 nativeGap111Raw.2.1 nativeGap111Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_112_valid :
    0 ≤ nativeGap112Raw.1 ∧ 0 ≤ nativeGap112Raw.2.1 ∧ 0 ≤ nativeGap112Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap112Raw.1
      (heatOldIncrement 112 nativeGap112Raw.1 nativeGap112Raw.2.1 nativeGap112Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_113_valid :
    0 ≤ nativeGap113Raw.1 ∧ 0 ≤ nativeGap113Raw.2.1 ∧ 0 ≤ nativeGap113Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap113Raw.1
      (heatOldIncrement 113 nativeGap113Raw.1 nativeGap113Raw.2.1 nativeGap113Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_114_valid :
    0 ≤ nativeGap114Raw.1 ∧ 0 ≤ nativeGap114Raw.2.1 ∧ 0 ≤ nativeGap114Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap114Raw.1
      (heatOldIncrement 114 nativeGap114Raw.1 nativeGap114Raw.2.1 nativeGap114Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_115_valid :
    0 ≤ nativeGap115Raw.1 ∧ 0 ≤ nativeGap115Raw.2.1 ∧ 0 ≤ nativeGap115Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap115Raw.1
      (heatOldIncrement 115 nativeGap115Raw.1 nativeGap115Raw.2.1 nativeGap115Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_116_valid :
    0 ≤ nativeGap116Raw.1 ∧ 0 ≤ nativeGap116Raw.2.1 ∧ 0 ≤ nativeGap116Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap116Raw.1
      (heatOldIncrement 116 nativeGap116Raw.1 nativeGap116Raw.2.1 nativeGap116Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_117_valid :
    0 ≤ nativeGap117Raw.1 ∧ 0 ≤ nativeGap117Raw.2.1 ∧ 0 ≤ nativeGap117Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap117Raw.1
      (heatOldIncrement 117 nativeGap117Raw.1 nativeGap117Raw.2.1 nativeGap117Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_118_valid :
    0 ≤ nativeGap118Raw.1 ∧ 0 ≤ nativeGap118Raw.2.1 ∧ 0 ≤ nativeGap118Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap118Raw.1
      (heatOldIncrement 118 nativeGap118Raw.1 nativeGap118Raw.2.1 nativeGap118Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_119_valid :
    0 ≤ nativeGap119Raw.1 ∧ 0 ≤ nativeGap119Raw.2.1 ∧ 0 ≤ nativeGap119Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap119Raw.1
      (heatOldIncrement 119 nativeGap119Raw.1 nativeGap119Raw.2.1 nativeGap119Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_120_valid :
    0 ≤ nativeGap120Raw.1 ∧ 0 ≤ nativeGap120Raw.2.1 ∧ 0 ≤ nativeGap120Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap120Raw.1
      (heatOldIncrement 120 nativeGap120Raw.1 nativeGap120Raw.2.1 nativeGap120Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_121_valid :
    0 ≤ nativeGap121Raw.1 ∧ 0 ≤ nativeGap121Raw.2.1 ∧ 0 ≤ nativeGap121Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap121Raw.1
      (heatOldIncrement 121 nativeGap121Raw.1 nativeGap121Raw.2.1 nativeGap121Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_122_valid :
    0 ≤ nativeGap122Raw.1 ∧ 0 ≤ nativeGap122Raw.2.1 ∧ 0 ≤ nativeGap122Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap122Raw.1
      (heatOldIncrement 122 nativeGap122Raw.1 nativeGap122Raw.2.1 nativeGap122Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_123_valid :
    0 ≤ nativeGap123Raw.1 ∧ 0 ≤ nativeGap123Raw.2.1 ∧ 0 ≤ nativeGap123Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap123Raw.1
      (heatOldIncrement 123 nativeGap123Raw.1 nativeGap123Raw.2.1 nativeGap123Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_124_valid :
    0 ≤ nativeGap124Raw.1 ∧ 0 ≤ nativeGap124Raw.2.1 ∧ 0 ≤ nativeGap124Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap124Raw.1
      (heatOldIncrement 124 nativeGap124Raw.1 nativeGap124Raw.2.1 nativeGap124Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_125_valid :
    0 ≤ nativeGap125Raw.1 ∧ 0 ≤ nativeGap125Raw.2.1 ∧ 0 ≤ nativeGap125Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap125Raw.1
      (heatOldIncrement 125 nativeGap125Raw.1 nativeGap125Raw.2.1 nativeGap125Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_126_valid :
    0 ≤ nativeGap126Raw.1 ∧ 0 ≤ nativeGap126Raw.2.1 ∧ 0 ≤ nativeGap126Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap126Raw.1
      (heatOldIncrement 126 nativeGap126Raw.1 nativeGap126Raw.2.1 nativeGap126Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_127_valid :
    0 ≤ nativeGap127Raw.1 ∧ 0 ≤ nativeGap127Raw.2.1 ∧ 0 ≤ nativeGap127Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap127Raw.1
      (heatOldIncrement 127 nativeGap127Raw.1 nativeGap127Raw.2.1 nativeGap127Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_128_valid :
    0 ≤ nativeGap128Raw.1 ∧ 0 ≤ nativeGap128Raw.2.1 ∧ 0 ≤ nativeGap128Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap128Raw.1
      (heatOldIncrement 128 nativeGap128Raw.1 nativeGap128Raw.2.1 nativeGap128Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

end ASDExplicitGamma.Native
