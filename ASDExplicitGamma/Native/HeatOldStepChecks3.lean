module

public import ASDExplicitGamma.Native.HeatOldStepCertificates

/-! Exact radical checks along the OLD producer path. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

-- Elaborate these kernel checks one at a time: with asynchronous elaboration the checks are held together
-- until the end of the file and peak at ~9 GiB; sequentially they peak at ~2 GiB for the same CPU time.
set_option Elab.async false

theorem heat_old_steps_129_valid :
    0 ≤ nativeGap129Raw.1 ∧ 0 ≤ nativeGap129Raw.2.1 ∧ 0 ≤ nativeGap129Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap129Raw.1
      (heatOldIncrement 129 nativeGap129Raw.1 nativeGap129Raw.2.1 nativeGap129Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_130_valid :
    0 ≤ nativeGap130Raw.1 ∧ 0 ≤ nativeGap130Raw.2.1 ∧ 0 ≤ nativeGap130Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap130Raw.1
      (heatOldIncrement 130 nativeGap130Raw.1 nativeGap130Raw.2.1 nativeGap130Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_131_valid :
    0 ≤ nativeGap131Raw.1 ∧ 0 ≤ nativeGap131Raw.2.1 ∧ 0 ≤ nativeGap131Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap131Raw.1
      (heatOldIncrement 131 nativeGap131Raw.1 nativeGap131Raw.2.1 nativeGap131Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_132_valid :
    0 ≤ nativeGap132Raw.1 ∧ 0 ≤ nativeGap132Raw.2.1 ∧ 0 ≤ nativeGap132Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap132Raw.1
      (heatOldIncrement 132 nativeGap132Raw.1 nativeGap132Raw.2.1 nativeGap132Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_133_valid :
    0 ≤ nativeGap133Raw.1 ∧ 0 ≤ nativeGap133Raw.2.1 ∧ 0 ≤ nativeGap133Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap133Raw.1
      (heatOldIncrement 133 nativeGap133Raw.1 nativeGap133Raw.2.1 nativeGap133Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_134_valid :
    0 ≤ nativeGap134Raw.1 ∧ 0 ≤ nativeGap134Raw.2.1 ∧ 0 ≤ nativeGap134Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap134Raw.1
      (heatOldIncrement 134 nativeGap134Raw.1 nativeGap134Raw.2.1 nativeGap134Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_135_valid :
    0 ≤ nativeGap135Raw.1 ∧ 0 ≤ nativeGap135Raw.2.1 ∧ 0 ≤ nativeGap135Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap135Raw.1
      (heatOldIncrement 135 nativeGap135Raw.1 nativeGap135Raw.2.1 nativeGap135Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_136_valid :
    0 ≤ nativeGap136Raw.1 ∧ 0 ≤ nativeGap136Raw.2.1 ∧ 0 ≤ nativeGap136Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap136Raw.1
      (heatOldIncrement 136 nativeGap136Raw.1 nativeGap136Raw.2.1 nativeGap136Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_137_valid :
    0 ≤ nativeGap137Raw.1 ∧ 0 ≤ nativeGap137Raw.2.1 ∧ 0 ≤ nativeGap137Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap137Raw.1
      (heatOldIncrement 137 nativeGap137Raw.1 nativeGap137Raw.2.1 nativeGap137Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_138_valid :
    0 ≤ nativeGap138Raw.1 ∧ 0 ≤ nativeGap138Raw.2.1 ∧ 0 ≤ nativeGap138Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap138Raw.1
      (heatOldIncrement 138 nativeGap138Raw.1 nativeGap138Raw.2.1 nativeGap138Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_139_valid :
    0 ≤ nativeGap139Raw.1 ∧ 0 ≤ nativeGap139Raw.2.1 ∧ 0 ≤ nativeGap139Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap139Raw.1
      (heatOldIncrement 139 nativeGap139Raw.1 nativeGap139Raw.2.1 nativeGap139Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_140_valid :
    0 ≤ nativeGap140Raw.1 ∧ 0 ≤ nativeGap140Raw.2.1 ∧ 0 ≤ nativeGap140Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap140Raw.1
      (heatOldIncrement 140 nativeGap140Raw.1 nativeGap140Raw.2.1 nativeGap140Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_141_valid :
    0 ≤ nativeGap141Raw.1 ∧ 0 ≤ nativeGap141Raw.2.1 ∧ 0 ≤ nativeGap141Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap141Raw.1
      (heatOldIncrement 141 nativeGap141Raw.1 nativeGap141Raw.2.1 nativeGap141Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_142_valid :
    0 ≤ nativeGap142Raw.1 ∧ 0 ≤ nativeGap142Raw.2.1 ∧ 0 ≤ nativeGap142Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap142Raw.1
      (heatOldIncrement 142 nativeGap142Raw.1 nativeGap142Raw.2.1 nativeGap142Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_143_valid :
    0 ≤ nativeGap143Raw.1 ∧ 0 ≤ nativeGap143Raw.2.1 ∧ 0 ≤ nativeGap143Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap143Raw.1
      (heatOldIncrement 143 nativeGap143Raw.1 nativeGap143Raw.2.1 nativeGap143Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_144_valid :
    0 ≤ nativeGap144Raw.1 ∧ 0 ≤ nativeGap144Raw.2.1 ∧ 0 ≤ nativeGap144Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap144Raw.1
      (heatOldIncrement 144 nativeGap144Raw.1 nativeGap144Raw.2.1 nativeGap144Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_145_valid :
    0 ≤ nativeGap145Raw.1 ∧ 0 ≤ nativeGap145Raw.2.1 ∧ 0 ≤ nativeGap145Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap145Raw.1
      (heatOldIncrement 145 nativeGap145Raw.1 nativeGap145Raw.2.1 nativeGap145Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_146_valid :
    0 ≤ nativeGap146Raw.1 ∧ 0 ≤ nativeGap146Raw.2.1 ∧ 0 ≤ nativeGap146Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap146Raw.1
      (heatOldIncrement 146 nativeGap146Raw.1 nativeGap146Raw.2.1 nativeGap146Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_147_valid :
    0 ≤ nativeGap147Raw.1 ∧ 0 ≤ nativeGap147Raw.2.1 ∧ 0 ≤ nativeGap147Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap147Raw.1
      (heatOldIncrement 147 nativeGap147Raw.1 nativeGap147Raw.2.1 nativeGap147Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_148_valid :
    0 ≤ nativeGap148Raw.1 ∧ 0 ≤ nativeGap148Raw.2.1 ∧ 0 ≤ nativeGap148Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap148Raw.1
      (heatOldIncrement 148 nativeGap148Raw.1 nativeGap148Raw.2.1 nativeGap148Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_149_valid :
    0 ≤ nativeGap149Raw.1 ∧ 0 ≤ nativeGap149Raw.2.1 ∧ 0 ≤ nativeGap149Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap149Raw.1
      (heatOldIncrement 149 nativeGap149Raw.1 nativeGap149Raw.2.1 nativeGap149Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_150_valid :
    0 ≤ nativeGap150Raw.1 ∧ 0 ≤ nativeGap150Raw.2.1 ∧ 0 ≤ nativeGap150Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap150Raw.1
      (heatOldIncrement 150 nativeGap150Raw.1 nativeGap150Raw.2.1 nativeGap150Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_151_valid :
    0 ≤ nativeGap151Raw.1 ∧ 0 ≤ nativeGap151Raw.2.1 ∧ 0 ≤ nativeGap151Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap151Raw.1
      (heatOldIncrement 151 nativeGap151Raw.1 nativeGap151Raw.2.1 nativeGap151Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_152_valid :
    0 ≤ nativeGap152Raw.1 ∧ 0 ≤ nativeGap152Raw.2.1 ∧ 0 ≤ nativeGap152Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap152Raw.1
      (heatOldIncrement 152 nativeGap152Raw.1 nativeGap152Raw.2.1 nativeGap152Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_153_valid :
    0 ≤ nativeGap153Raw.1 ∧ 0 ≤ nativeGap153Raw.2.1 ∧ 0 ≤ nativeGap153Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap153Raw.1
      (heatOldIncrement 153 nativeGap153Raw.1 nativeGap153Raw.2.1 nativeGap153Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_154_valid :
    0 ≤ nativeGap154Raw.1 ∧ 0 ≤ nativeGap154Raw.2.1 ∧ 0 ≤ nativeGap154Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap154Raw.1
      (heatOldIncrement 154 nativeGap154Raw.1 nativeGap154Raw.2.1 nativeGap154Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_155_valid :
    0 ≤ nativeGap155Raw.1 ∧ 0 ≤ nativeGap155Raw.2.1 ∧ 0 ≤ nativeGap155Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap155Raw.1
      (heatOldIncrement 155 nativeGap155Raw.1 nativeGap155Raw.2.1 nativeGap155Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_156_valid :
    0 ≤ nativeGap156Raw.1 ∧ 0 ≤ nativeGap156Raw.2.1 ∧ 0 ≤ nativeGap156Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap156Raw.1
      (heatOldIncrement 156 nativeGap156Raw.1 nativeGap156Raw.2.1 nativeGap156Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_157_valid :
    0 ≤ nativeGap157Raw.1 ∧ 0 ≤ nativeGap157Raw.2.1 ∧ 0 ≤ nativeGap157Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap157Raw.1
      (heatOldIncrement 157 nativeGap157Raw.1 nativeGap157Raw.2.1 nativeGap157Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_158_valid :
    0 ≤ nativeGap158Raw.1 ∧ 0 ≤ nativeGap158Raw.2.1 ∧ 0 ≤ nativeGap158Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap158Raw.1
      (heatOldIncrement 158 nativeGap158Raw.1 nativeGap158Raw.2.1 nativeGap158Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_159_valid :
    0 ≤ nativeGap159Raw.1 ∧ 0 ≤ nativeGap159Raw.2.1 ∧ 0 ≤ nativeGap159Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap159Raw.1
      (heatOldIncrement 159 nativeGap159Raw.1 nativeGap159Raw.2.1 nativeGap159Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_160_valid :
    0 ≤ nativeGap160Raw.1 ∧ 0 ≤ nativeGap160Raw.2.1 ∧ 0 ≤ nativeGap160Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap160Raw.1
      (heatOldIncrement 160 nativeGap160Raw.1 nativeGap160Raw.2.1 nativeGap160Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

theorem heat_old_steps_161_valid :
    0 ≤ nativeGap161Raw.1 ∧ 0 ≤ nativeGap161Raw.2.1 ∧ 0 ≤ nativeGap161Raw.2.2 ∧
    ∀ i : Fin 4,HeatOldStepValid nativeGap161Raw.1
      (heatOldIncrement 161 nativeGap161Raw.1 nativeGap161Raw.2.1 nativeGap161Raw.2.2 i.val) := by
  unfold HeatOldStepValid
  decide +kernel

end ASDExplicitGamma.Native
