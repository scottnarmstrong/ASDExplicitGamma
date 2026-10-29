module

public import ASDExplicitGamma.Native.HeatConfiguredSourceRows

/-! Positivity and the two exact rare-ratio roots for every configured OLD row. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

/-- Arithmetic validity needed to consume an individual OLD source row. -/
def HeatIndividualOldValid (old : NativeOldRow) : Prop :=
  0 ≤ old.e ∧ 0 < old.x ∧ 0 ≤ old.f ∧
    nativeRootValid ((old.f/old.x)^5) 27 = true ∧
    nativeRootValid ((old.f/old.x)^10) 27 = true

theorem heat_individual_old_001_valid : HeatIndividualOldValid nativeGap001Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_010_valid : HeatIndividualOldValid nativeGap010Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_011_valid : HeatIndividualOldValid nativeGap011Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_012_valid : HeatIndividualOldValid nativeGap012Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_013_valid : HeatIndividualOldValid nativeGap013Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_014_valid : HeatIndividualOldValid nativeGap014Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_015_valid : HeatIndividualOldValid nativeGap015Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_016_valid : HeatIndividualOldValid nativeGap016Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_017_valid : HeatIndividualOldValid nativeGap017Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_018_valid : HeatIndividualOldValid nativeGap018Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_019_valid : HeatIndividualOldValid nativeGap019Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_020_valid : HeatIndividualOldValid nativeGap020Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_021_valid : HeatIndividualOldValid nativeGap021Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_022_valid : HeatIndividualOldValid nativeGap022Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_023_valid : HeatIndividualOldValid nativeGap023Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_024_valid : HeatIndividualOldValid nativeGap024Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_025_valid : HeatIndividualOldValid nativeGap025Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_026_valid : HeatIndividualOldValid nativeGap026Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_027_valid : HeatIndividualOldValid nativeGap027Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_028_valid : HeatIndividualOldValid nativeGap028Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_029_valid : HeatIndividualOldValid nativeGap029Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_030_valid : HeatIndividualOldValid nativeGap030Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_031_valid : HeatIndividualOldValid nativeGap031Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_032_valid : HeatIndividualOldValid nativeGap032Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_033_valid : HeatIndividualOldValid nativeGap033Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_034_valid : HeatIndividualOldValid nativeGap034Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_035_valid : HeatIndividualOldValid nativeGap035Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_036_valid : HeatIndividualOldValid nativeGap036Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_037_valid : HeatIndividualOldValid nativeGap037Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_038_valid : HeatIndividualOldValid nativeGap038Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_039_valid : HeatIndividualOldValid nativeGap039Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_040_valid : HeatIndividualOldValid nativeGap040Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_041_valid : HeatIndividualOldValid nativeGap041Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_042_valid : HeatIndividualOldValid nativeGap042Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_043_valid : HeatIndividualOldValid nativeGap043Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_044_valid : HeatIndividualOldValid nativeGap044Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_045_valid : HeatIndividualOldValid nativeGap045Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_046_valid : HeatIndividualOldValid nativeGap046Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_047_valid : HeatIndividualOldValid nativeGap047Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_048_valid : HeatIndividualOldValid nativeGap048Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_049_valid : HeatIndividualOldValid nativeGap049Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_050_valid : HeatIndividualOldValid nativeGap050Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_051_valid : HeatIndividualOldValid nativeGap051Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_052_valid : HeatIndividualOldValid nativeGap052Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_053_valid : HeatIndividualOldValid nativeGap053Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_054_valid : HeatIndividualOldValid nativeGap054Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_055_valid : HeatIndividualOldValid nativeGap055Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_056_valid : HeatIndividualOldValid nativeGap056Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_057_valid : HeatIndividualOldValid nativeGap057Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_058_valid : HeatIndividualOldValid nativeGap058Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_059_valid : HeatIndividualOldValid nativeGap059Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_060_valid : HeatIndividualOldValid nativeGap060Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_061_valid : HeatIndividualOldValid nativeGap061Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_062_valid : HeatIndividualOldValid nativeGap062Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_063_valid : HeatIndividualOldValid nativeGap063Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_064_valid : HeatIndividualOldValid nativeGap064Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_065_valid : HeatIndividualOldValid nativeGap065Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_066_valid : HeatIndividualOldValid nativeGap066Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_067_valid : HeatIndividualOldValid nativeGap067Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_068_valid : HeatIndividualOldValid nativeGap068Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_069_valid : HeatIndividualOldValid nativeGap069Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_070_valid : HeatIndividualOldValid nativeGap070Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_071_valid : HeatIndividualOldValid nativeGap071Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_072_valid : HeatIndividualOldValid nativeGap072Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_073_valid : HeatIndividualOldValid nativeGap073Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_074_valid : HeatIndividualOldValid nativeGap074Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_075_valid : HeatIndividualOldValid nativeGap075Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_076_valid : HeatIndividualOldValid nativeGap076Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_077_valid : HeatIndividualOldValid nativeGap077Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_078_valid : HeatIndividualOldValid nativeGap078Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_079_valid : HeatIndividualOldValid nativeGap079Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_080_valid : HeatIndividualOldValid nativeGap080Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_081_valid : HeatIndividualOldValid nativeGap081Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_082_valid : HeatIndividualOldValid nativeGap082Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_083_valid : HeatIndividualOldValid nativeGap083Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_084_valid : HeatIndividualOldValid nativeGap084Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_085_valid : HeatIndividualOldValid nativeGap085Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_086_valid : HeatIndividualOldValid nativeGap086Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_087_valid : HeatIndividualOldValid nativeGap087Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_088_valid : HeatIndividualOldValid nativeGap088Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_089_valid : HeatIndividualOldValid nativeGap089Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_090_valid : HeatIndividualOldValid nativeGap090Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_091_valid : HeatIndividualOldValid nativeGap091Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_092_valid : HeatIndividualOldValid nativeGap092Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_093_valid : HeatIndividualOldValid nativeGap093Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_094_valid : HeatIndividualOldValid nativeGap094Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_095_valid : HeatIndividualOldValid nativeGap095Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_096_valid : HeatIndividualOldValid nativeGap096Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_097_valid : HeatIndividualOldValid nativeGap097Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_098_valid : HeatIndividualOldValid nativeGap098Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_099_valid : HeatIndividualOldValid nativeGap099Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_100_valid : HeatIndividualOldValid nativeGap100Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_101_valid : HeatIndividualOldValid nativeGap101Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_102_valid : HeatIndividualOldValid nativeGap102Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_103_valid : HeatIndividualOldValid nativeGap103Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_104_valid : HeatIndividualOldValid nativeGap104Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_105_valid : HeatIndividualOldValid nativeGap105Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_106_valid : HeatIndividualOldValid nativeGap106Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_107_valid : HeatIndividualOldValid nativeGap107Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_108_valid : HeatIndividualOldValid nativeGap108Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_109_valid : HeatIndividualOldValid nativeGap109Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_110_valid : HeatIndividualOldValid nativeGap110Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_111_valid : HeatIndividualOldValid nativeGap111Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_112_valid : HeatIndividualOldValid nativeGap112Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_113_valid : HeatIndividualOldValid nativeGap113Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_114_valid : HeatIndividualOldValid nativeGap114Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_115_valid : HeatIndividualOldValid nativeGap115Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_116_valid : HeatIndividualOldValid nativeGap116Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_117_valid : HeatIndividualOldValid nativeGap117Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_118_valid : HeatIndividualOldValid nativeGap118Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_119_valid : HeatIndividualOldValid nativeGap119Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_120_valid : HeatIndividualOldValid nativeGap120Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_121_valid : HeatIndividualOldValid nativeGap121Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_122_valid : HeatIndividualOldValid nativeGap122Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_123_valid : HeatIndividualOldValid nativeGap123Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_124_valid : HeatIndividualOldValid nativeGap124Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_125_valid : HeatIndividualOldValid nativeGap125Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_126_valid : HeatIndividualOldValid nativeGap126Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_127_valid : HeatIndividualOldValid nativeGap127Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_128_valid : HeatIndividualOldValid nativeGap128Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_129_valid : HeatIndividualOldValid nativeGap129Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_130_valid : HeatIndividualOldValid nativeGap130Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_131_valid : HeatIndividualOldValid nativeGap131Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_132_valid : HeatIndividualOldValid nativeGap132Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_133_valid : HeatIndividualOldValid nativeGap133Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_134_valid : HeatIndividualOldValid nativeGap134Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_135_valid : HeatIndividualOldValid nativeGap135Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_136_valid : HeatIndividualOldValid nativeGap136Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_137_valid : HeatIndividualOldValid nativeGap137Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_138_valid : HeatIndividualOldValid nativeGap138Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_139_valid : HeatIndividualOldValid nativeGap139Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_140_valid : HeatIndividualOldValid nativeGap140Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_141_valid : HeatIndividualOldValid nativeGap141Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_142_valid : HeatIndividualOldValid nativeGap142Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_143_valid : HeatIndividualOldValid nativeGap143Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_144_valid : HeatIndividualOldValid nativeGap144Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_145_valid : HeatIndividualOldValid nativeGap145Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_146_valid : HeatIndividualOldValid nativeGap146Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_147_valid : HeatIndividualOldValid nativeGap147Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_148_valid : HeatIndividualOldValid nativeGap148Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_149_valid : HeatIndividualOldValid nativeGap149Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_150_valid : HeatIndividualOldValid nativeGap150Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_151_valid : HeatIndividualOldValid nativeGap151Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_152_valid : HeatIndividualOldValid nativeGap152Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_153_valid : HeatIndividualOldValid nativeGap153Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_154_valid : HeatIndividualOldValid nativeGap154Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_155_valid : HeatIndividualOldValid nativeGap155Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_156_valid : HeatIndividualOldValid nativeGap156Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_157_valid : HeatIndividualOldValid nativeGap157Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_158_valid : HeatIndividualOldValid nativeGap158Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_159_valid : HeatIndividualOldValid nativeGap159Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_160_valid : HeatIndividualOldValid nativeGap160Old := by
  unfold HeatIndividualOldValid
  decide +kernel

theorem heat_individual_old_161_valid : HeatIndividualOldValid nativeGap161Old := by
  unfold HeatIndividualOldValid
  decide +kernel

/-- All153 selected OLD rows have their original, unshifted rare roots checked. -/
theorem heat_configured_individual_old_valid (j : Fin 153) :
    HeatIndividualOldValid (nativeOld (nativeConfiguredSystem j).gap) := by
  fin_cases j
  · change HeatIndividualOldValid (nativeOld 1)
    rw [nativeGap001Old_source]
    exact heat_individual_old_001_valid
  · change HeatIndividualOldValid (nativeOld 10)
    rw [nativeGap010Old_source]
    exact heat_individual_old_010_valid
  · change HeatIndividualOldValid (nativeOld 11)
    rw [nativeGap011Old_source]
    exact heat_individual_old_011_valid
  · change HeatIndividualOldValid (nativeOld 12)
    rw [nativeGap012Old_source]
    exact heat_individual_old_012_valid
  · change HeatIndividualOldValid (nativeOld 13)
    rw [nativeGap013Old_source]
    exact heat_individual_old_013_valid
  · change HeatIndividualOldValid (nativeOld 14)
    rw [nativeGap014Old_source]
    exact heat_individual_old_014_valid
  · change HeatIndividualOldValid (nativeOld 15)
    rw [nativeGap015Old_source]
    exact heat_individual_old_015_valid
  · change HeatIndividualOldValid (nativeOld 16)
    rw [nativeGap016Old_source]
    exact heat_individual_old_016_valid
  · change HeatIndividualOldValid (nativeOld 17)
    rw [nativeGap017Old_source]
    exact heat_individual_old_017_valid
  · change HeatIndividualOldValid (nativeOld 18)
    rw [nativeGap018Old_source]
    exact heat_individual_old_018_valid
  · change HeatIndividualOldValid (nativeOld 19)
    rw [nativeGap019Old_source]
    exact heat_individual_old_019_valid
  · change HeatIndividualOldValid (nativeOld 20)
    rw [nativeGap020Old_source]
    exact heat_individual_old_020_valid
  · change HeatIndividualOldValid (nativeOld 21)
    rw [nativeGap021Old_source]
    exact heat_individual_old_021_valid
  · change HeatIndividualOldValid (nativeOld 22)
    rw [nativeGap022Old_source]
    exact heat_individual_old_022_valid
  · change HeatIndividualOldValid (nativeOld 23)
    rw [nativeGap023Old_source]
    exact heat_individual_old_023_valid
  · change HeatIndividualOldValid (nativeOld 24)
    rw [nativeGap024Old_source]
    exact heat_individual_old_024_valid
  · change HeatIndividualOldValid (nativeOld 25)
    rw [nativeGap025Old_source]
    exact heat_individual_old_025_valid
  · change HeatIndividualOldValid (nativeOld 26)
    rw [nativeGap026Old_source]
    exact heat_individual_old_026_valid
  · change HeatIndividualOldValid (nativeOld 27)
    rw [nativeGap027Old_source]
    exact heat_individual_old_027_valid
  · change HeatIndividualOldValid (nativeOld 28)
    rw [nativeGap028Old_source]
    exact heat_individual_old_028_valid
  · change HeatIndividualOldValid (nativeOld 29)
    rw [nativeGap029Old_source]
    exact heat_individual_old_029_valid
  · change HeatIndividualOldValid (nativeOld 30)
    rw [nativeGap030Old_source]
    exact heat_individual_old_030_valid
  · change HeatIndividualOldValid (nativeOld 31)
    rw [nativeGap031Old_source]
    exact heat_individual_old_031_valid
  · change HeatIndividualOldValid (nativeOld 32)
    rw [nativeGap032Old_source]
    exact heat_individual_old_032_valid
  · change HeatIndividualOldValid (nativeOld 33)
    rw [nativeGap033Old_source]
    exact heat_individual_old_033_valid
  · change HeatIndividualOldValid (nativeOld 34)
    rw [nativeGap034Old_source]
    exact heat_individual_old_034_valid
  · change HeatIndividualOldValid (nativeOld 35)
    rw [nativeGap035Old_source]
    exact heat_individual_old_035_valid
  · change HeatIndividualOldValid (nativeOld 36)
    rw [nativeGap036Old_source]
    exact heat_individual_old_036_valid
  · change HeatIndividualOldValid (nativeOld 37)
    rw [nativeGap037Old_source]
    exact heat_individual_old_037_valid
  · change HeatIndividualOldValid (nativeOld 38)
    rw [nativeGap038Old_source]
    exact heat_individual_old_038_valid
  · change HeatIndividualOldValid (nativeOld 39)
    rw [nativeGap039Old_source]
    exact heat_individual_old_039_valid
  · change HeatIndividualOldValid (nativeOld 40)
    rw [nativeGap040Old_source]
    exact heat_individual_old_040_valid
  · change HeatIndividualOldValid (nativeOld 41)
    rw [nativeGap041Old_source]
    exact heat_individual_old_041_valid
  · change HeatIndividualOldValid (nativeOld 42)
    rw [nativeGap042Old_source]
    exact heat_individual_old_042_valid
  · change HeatIndividualOldValid (nativeOld 43)
    rw [nativeGap043Old_source]
    exact heat_individual_old_043_valid
  · change HeatIndividualOldValid (nativeOld 44)
    rw [nativeGap044Old_source]
    exact heat_individual_old_044_valid
  · change HeatIndividualOldValid (nativeOld 45)
    rw [nativeGap045Old_source]
    exact heat_individual_old_045_valid
  · change HeatIndividualOldValid (nativeOld 46)
    rw [nativeGap046Old_source]
    exact heat_individual_old_046_valid
  · change HeatIndividualOldValid (nativeOld 47)
    rw [nativeGap047Old_source]
    exact heat_individual_old_047_valid
  · change HeatIndividualOldValid (nativeOld 48)
    rw [nativeGap048Old_source]
    exact heat_individual_old_048_valid
  · change HeatIndividualOldValid (nativeOld 49)
    rw [nativeGap049Old_source]
    exact heat_individual_old_049_valid
  · change HeatIndividualOldValid (nativeOld 50)
    rw [nativeGap050Old_source]
    exact heat_individual_old_050_valid
  · change HeatIndividualOldValid (nativeOld 51)
    rw [nativeGap051Old_source]
    exact heat_individual_old_051_valid
  · change HeatIndividualOldValid (nativeOld 52)
    rw [nativeGap052Old_source]
    exact heat_individual_old_052_valid
  · change HeatIndividualOldValid (nativeOld 53)
    rw [nativeGap053Old_source]
    exact heat_individual_old_053_valid
  · change HeatIndividualOldValid (nativeOld 54)
    rw [nativeGap054Old_source]
    exact heat_individual_old_054_valid
  · change HeatIndividualOldValid (nativeOld 55)
    rw [nativeGap055Old_source]
    exact heat_individual_old_055_valid
  · change HeatIndividualOldValid (nativeOld 56)
    rw [nativeGap056Old_source]
    exact heat_individual_old_056_valid
  · change HeatIndividualOldValid (nativeOld 57)
    rw [nativeGap057Old_source]
    exact heat_individual_old_057_valid
  · change HeatIndividualOldValid (nativeOld 58)
    rw [nativeGap058Old_source]
    exact heat_individual_old_058_valid
  · change HeatIndividualOldValid (nativeOld 59)
    rw [nativeGap059Old_source]
    exact heat_individual_old_059_valid
  · change HeatIndividualOldValid (nativeOld 60)
    rw [nativeGap060Old_source]
    exact heat_individual_old_060_valid
  · change HeatIndividualOldValid (nativeOld 61)
    rw [nativeGap061Old_source]
    exact heat_individual_old_061_valid
  · change HeatIndividualOldValid (nativeOld 62)
    rw [nativeGap062Old_source]
    exact heat_individual_old_062_valid
  · change HeatIndividualOldValid (nativeOld 63)
    rw [nativeGap063Old_source]
    exact heat_individual_old_063_valid
  · change HeatIndividualOldValid (nativeOld 64)
    rw [nativeGap064Old_source]
    exact heat_individual_old_064_valid
  · change HeatIndividualOldValid (nativeOld 65)
    rw [nativeGap065Old_source]
    exact heat_individual_old_065_valid
  · change HeatIndividualOldValid (nativeOld 66)
    rw [nativeGap066Old_source]
    exact heat_individual_old_066_valid
  · change HeatIndividualOldValid (nativeOld 67)
    rw [nativeGap067Old_source]
    exact heat_individual_old_067_valid
  · change HeatIndividualOldValid (nativeOld 68)
    rw [nativeGap068Old_source]
    exact heat_individual_old_068_valid
  · change HeatIndividualOldValid (nativeOld 69)
    rw [nativeGap069Old_source]
    exact heat_individual_old_069_valid
  · change HeatIndividualOldValid (nativeOld 70)
    rw [nativeGap070Old_source]
    exact heat_individual_old_070_valid
  · change HeatIndividualOldValid (nativeOld 71)
    rw [nativeGap071Old_source]
    exact heat_individual_old_071_valid
  · change HeatIndividualOldValid (nativeOld 72)
    rw [nativeGap072Old_source]
    exact heat_individual_old_072_valid
  · change HeatIndividualOldValid (nativeOld 73)
    rw [nativeGap073Old_source]
    exact heat_individual_old_073_valid
  · change HeatIndividualOldValid (nativeOld 74)
    rw [nativeGap074Old_source]
    exact heat_individual_old_074_valid
  · change HeatIndividualOldValid (nativeOld 75)
    rw [nativeGap075Old_source]
    exact heat_individual_old_075_valid
  · change HeatIndividualOldValid (nativeOld 76)
    rw [nativeGap076Old_source]
    exact heat_individual_old_076_valid
  · change HeatIndividualOldValid (nativeOld 77)
    rw [nativeGap077Old_source]
    exact heat_individual_old_077_valid
  · change HeatIndividualOldValid (nativeOld 78)
    rw [nativeGap078Old_source]
    exact heat_individual_old_078_valid
  · change HeatIndividualOldValid (nativeOld 79)
    rw [nativeGap079Old_source]
    exact heat_individual_old_079_valid
  · change HeatIndividualOldValid (nativeOld 80)
    rw [nativeGap080Old_source]
    exact heat_individual_old_080_valid
  · change HeatIndividualOldValid (nativeOld 81)
    rw [nativeGap081Old_source]
    exact heat_individual_old_081_valid
  · change HeatIndividualOldValid (nativeOld 82)
    rw [nativeGap082Old_source]
    exact heat_individual_old_082_valid
  · change HeatIndividualOldValid (nativeOld 83)
    rw [nativeGap083Old_source]
    exact heat_individual_old_083_valid
  · change HeatIndividualOldValid (nativeOld 84)
    rw [nativeGap084Old_source]
    exact heat_individual_old_084_valid
  · change HeatIndividualOldValid (nativeOld 85)
    rw [nativeGap085Old_source]
    exact heat_individual_old_085_valid
  · change HeatIndividualOldValid (nativeOld 86)
    rw [nativeGap086Old_source]
    exact heat_individual_old_086_valid
  · change HeatIndividualOldValid (nativeOld 87)
    rw [nativeGap087Old_source]
    exact heat_individual_old_087_valid
  · change HeatIndividualOldValid (nativeOld 88)
    rw [nativeGap088Old_source]
    exact heat_individual_old_088_valid
  · change HeatIndividualOldValid (nativeOld 89)
    rw [nativeGap089Old_source]
    exact heat_individual_old_089_valid
  · change HeatIndividualOldValid (nativeOld 90)
    rw [nativeGap090Old_source]
    exact heat_individual_old_090_valid
  · change HeatIndividualOldValid (nativeOld 91)
    rw [nativeGap091Old_source]
    exact heat_individual_old_091_valid
  · change HeatIndividualOldValid (nativeOld 92)
    rw [nativeGap092Old_source]
    exact heat_individual_old_092_valid
  · change HeatIndividualOldValid (nativeOld 93)
    rw [nativeGap093Old_source]
    exact heat_individual_old_093_valid
  · change HeatIndividualOldValid (nativeOld 94)
    rw [nativeGap094Old_source]
    exact heat_individual_old_094_valid
  · change HeatIndividualOldValid (nativeOld 95)
    rw [nativeGap095Old_source]
    exact heat_individual_old_095_valid
  · change HeatIndividualOldValid (nativeOld 96)
    rw [nativeGap096Old_source]
    exact heat_individual_old_096_valid
  · change HeatIndividualOldValid (nativeOld 97)
    rw [nativeGap097Old_source]
    exact heat_individual_old_097_valid
  · change HeatIndividualOldValid (nativeOld 98)
    rw [nativeGap098Old_source]
    exact heat_individual_old_098_valid
  · change HeatIndividualOldValid (nativeOld 99)
    rw [nativeGap099Old_source]
    exact heat_individual_old_099_valid
  · change HeatIndividualOldValid (nativeOld 100)
    rw [nativeGap100Old_source]
    exact heat_individual_old_100_valid
  · change HeatIndividualOldValid (nativeOld 101)
    rw [nativeGap101Old_source]
    exact heat_individual_old_101_valid
  · change HeatIndividualOldValid (nativeOld 102)
    rw [nativeGap102Old_source]
    exact heat_individual_old_102_valid
  · change HeatIndividualOldValid (nativeOld 103)
    rw [nativeGap103Old_source]
    exact heat_individual_old_103_valid
  · change HeatIndividualOldValid (nativeOld 104)
    rw [nativeGap104Old_source]
    exact heat_individual_old_104_valid
  · change HeatIndividualOldValid (nativeOld 105)
    rw [nativeGap105Old_source]
    exact heat_individual_old_105_valid
  · change HeatIndividualOldValid (nativeOld 106)
    rw [nativeGap106Old_source]
    exact heat_individual_old_106_valid
  · change HeatIndividualOldValid (nativeOld 107)
    rw [nativeGap107Old_source]
    exact heat_individual_old_107_valid
  · change HeatIndividualOldValid (nativeOld 108)
    rw [nativeGap108Old_source]
    exact heat_individual_old_108_valid
  · change HeatIndividualOldValid (nativeOld 109)
    rw [nativeGap109Old_source]
    exact heat_individual_old_109_valid
  · change HeatIndividualOldValid (nativeOld 110)
    rw [nativeGap110Old_source]
    exact heat_individual_old_110_valid
  · change HeatIndividualOldValid (nativeOld 111)
    rw [nativeGap111Old_source]
    exact heat_individual_old_111_valid
  · change HeatIndividualOldValid (nativeOld 112)
    rw [nativeGap112Old_source]
    exact heat_individual_old_112_valid
  · change HeatIndividualOldValid (nativeOld 113)
    rw [nativeGap113Old_source]
    exact heat_individual_old_113_valid
  · change HeatIndividualOldValid (nativeOld 114)
    rw [nativeGap114Old_source]
    exact heat_individual_old_114_valid
  · change HeatIndividualOldValid (nativeOld 115)
    rw [nativeGap115Old_source]
    exact heat_individual_old_115_valid
  · change HeatIndividualOldValid (nativeOld 116)
    rw [nativeGap116Old_source]
    exact heat_individual_old_116_valid
  · change HeatIndividualOldValid (nativeOld 117)
    rw [nativeGap117Old_source]
    exact heat_individual_old_117_valid
  · change HeatIndividualOldValid (nativeOld 118)
    rw [nativeGap118Old_source]
    exact heat_individual_old_118_valid
  · change HeatIndividualOldValid (nativeOld 119)
    rw [nativeGap119Old_source]
    exact heat_individual_old_119_valid
  · change HeatIndividualOldValid (nativeOld 120)
    rw [nativeGap120Old_source]
    exact heat_individual_old_120_valid
  · change HeatIndividualOldValid (nativeOld 121)
    rw [nativeGap121Old_source]
    exact heat_individual_old_121_valid
  · change HeatIndividualOldValid (nativeOld 122)
    rw [nativeGap122Old_source]
    exact heat_individual_old_122_valid
  · change HeatIndividualOldValid (nativeOld 123)
    rw [nativeGap123Old_source]
    exact heat_individual_old_123_valid
  · change HeatIndividualOldValid (nativeOld 124)
    rw [nativeGap124Old_source]
    exact heat_individual_old_124_valid
  · change HeatIndividualOldValid (nativeOld 125)
    rw [nativeGap125Old_source]
    exact heat_individual_old_125_valid
  · change HeatIndividualOldValid (nativeOld 126)
    rw [nativeGap126Old_source]
    exact heat_individual_old_126_valid
  · change HeatIndividualOldValid (nativeOld 127)
    rw [nativeGap127Old_source]
    exact heat_individual_old_127_valid
  · change HeatIndividualOldValid (nativeOld 128)
    rw [nativeGap128Old_source]
    exact heat_individual_old_128_valid
  · change HeatIndividualOldValid (nativeOld 129)
    rw [nativeGap129Old_source]
    exact heat_individual_old_129_valid
  · change HeatIndividualOldValid (nativeOld 130)
    rw [nativeGap130Old_source]
    exact heat_individual_old_130_valid
  · change HeatIndividualOldValid (nativeOld 131)
    rw [nativeGap131Old_source]
    exact heat_individual_old_131_valid
  · change HeatIndividualOldValid (nativeOld 132)
    rw [nativeGap132Old_source]
    exact heat_individual_old_132_valid
  · change HeatIndividualOldValid (nativeOld 133)
    rw [nativeGap133Old_source]
    exact heat_individual_old_133_valid
  · change HeatIndividualOldValid (nativeOld 134)
    rw [nativeGap134Old_source]
    exact heat_individual_old_134_valid
  · change HeatIndividualOldValid (nativeOld 135)
    rw [nativeGap135Old_source]
    exact heat_individual_old_135_valid
  · change HeatIndividualOldValid (nativeOld 136)
    rw [nativeGap136Old_source]
    exact heat_individual_old_136_valid
  · change HeatIndividualOldValid (nativeOld 137)
    rw [nativeGap137Old_source]
    exact heat_individual_old_137_valid
  · change HeatIndividualOldValid (nativeOld 138)
    rw [nativeGap138Old_source]
    exact heat_individual_old_138_valid
  · change HeatIndividualOldValid (nativeOld 139)
    rw [nativeGap139Old_source]
    exact heat_individual_old_139_valid
  · change HeatIndividualOldValid (nativeOld 140)
    rw [nativeGap140Old_source]
    exact heat_individual_old_140_valid
  · change HeatIndividualOldValid (nativeOld 141)
    rw [nativeGap141Old_source]
    exact heat_individual_old_141_valid
  · change HeatIndividualOldValid (nativeOld 142)
    rw [nativeGap142Old_source]
    exact heat_individual_old_142_valid
  · change HeatIndividualOldValid (nativeOld 143)
    rw [nativeGap143Old_source]
    exact heat_individual_old_143_valid
  · change HeatIndividualOldValid (nativeOld 144)
    rw [nativeGap144Old_source]
    exact heat_individual_old_144_valid
  · change HeatIndividualOldValid (nativeOld 145)
    rw [nativeGap145Old_source]
    exact heat_individual_old_145_valid
  · change HeatIndividualOldValid (nativeOld 146)
    rw [nativeGap146Old_source]
    exact heat_individual_old_146_valid
  · change HeatIndividualOldValid (nativeOld 147)
    rw [nativeGap147Old_source]
    exact heat_individual_old_147_valid
  · change HeatIndividualOldValid (nativeOld 148)
    rw [nativeGap148Old_source]
    exact heat_individual_old_148_valid
  · change HeatIndividualOldValid (nativeOld 149)
    rw [nativeGap149Old_source]
    exact heat_individual_old_149_valid
  · change HeatIndividualOldValid (nativeOld 150)
    rw [nativeGap150Old_source]
    exact heat_individual_old_150_valid
  · change HeatIndividualOldValid (nativeOld 151)
    rw [nativeGap151Old_source]
    exact heat_individual_old_151_valid
  · change HeatIndividualOldValid (nativeOld 152)
    rw [nativeGap152Old_source]
    exact heat_individual_old_152_valid
  · change HeatIndividualOldValid (nativeOld 153)
    rw [nativeGap153Old_source]
    exact heat_individual_old_153_valid
  · change HeatIndividualOldValid (nativeOld 154)
    rw [nativeGap154Old_source]
    exact heat_individual_old_154_valid
  · change HeatIndividualOldValid (nativeOld 155)
    rw [nativeGap155Old_source]
    exact heat_individual_old_155_valid
  · change HeatIndividualOldValid (nativeOld 156)
    rw [nativeGap156Old_source]
    exact heat_individual_old_156_valid
  · change HeatIndividualOldValid (nativeOld 157)
    rw [nativeGap157Old_source]
    exact heat_individual_old_157_valid
  · change HeatIndividualOldValid (nativeOld 158)
    rw [nativeGap158Old_source]
    exact heat_individual_old_158_valid
  · change HeatIndividualOldValid (nativeOld 159)
    rw [nativeGap159Old_source]
    exact heat_individual_old_159_valid
  · change HeatIndividualOldValid (nativeOld 160)
    rw [nativeGap160Old_source]
    exact heat_individual_old_160_valid
  · change HeatIndividualOldValid (nativeOld 161)
    rw [nativeGap161Old_source]
    exact heat_individual_old_161_valid

end ASDExplicitGamma.Native
