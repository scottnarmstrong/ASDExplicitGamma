module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat076Complete
public import ASDExplicitGamma.Numerics.Native.Gap077Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_076_Gen : nativeHeatOldRowGen 76 = nativeGap077Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_076_Gen : nativeHeatIndividualGen 76 = nativeGap077Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_076_Gen : nativeHeatGenVariance 76 = nativeHeat076Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_076_Gen, nativeHeat076Variance_formula]

theorem nativeHeatStep_hSpec_076_Gen : nativeHeatGenSpectral 76 = nativeHeat076Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_076_Gen, nativeHeat076Variance_formula]

theorem nativeHeatStep_hQm_076_Gen : nativeHeatGenQm 76 = nativeHeat076Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_076_Gen, nativeHeatStep_hSpec_076_Gen,
    nativeHeat076Qm_formula]

theorem nativeHeatStep_hQN_076_Gen : nativeHeatQNGen 76 = nativeHeat076QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_076_Gen, nativeHeat076QN_formula]

theorem nativeHeatStep_hFr_076_Gen : nativeHeatFramesGen 76 = nativeHeat076Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_076_Gen, nativeHeatStep_hInd_076_Gen,
    nativeHeatStep_hVar_076_Gen, nativeHeatStep_hQN_076_Gen, nativeHeat076Frames_formula]

theorem nativeHeatStep_hArg_076_Gen : nativeHeatExpArgGen 76 = nativeHeatExpArg nativeGap077Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_076_Gen]

theorem nativeHeatStep_hExp_076_Gen : nativeHeatExpGen 76 = nativeHeat076Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_076_Gen, nativeHeat076Exp_formula]

theorem nativeHeatStep_hCoef_076_Gen : nativeHeatCoefGen 76 = nativeHeat076Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_076_Gen, nativeHeat076Coef_formula]

theorem nativeHeatStep_hInit_076_Gen : nativeHeatInitGen 76 = nativeHeat076Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_076_Gen, nativeHeatStep_hVar_076_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat076Init00_formula
    · exact nativeHeat076Init01_formula
    · exact nativeHeat076Init02_formula
    · exact nativeHeat076Init03_formula
    · exact nativeHeat076Init04_formula
    · exact nativeHeat076Init05_formula
    · exact nativeHeat076Init06_formula
    · exact nativeHeat076Init07_formula
    · exact nativeHeat076Init08_formula
    · exact nativeHeat076Init09_formula
    · exact nativeHeat076Init10_formula
    · exact nativeHeat076Init11_formula
    · exact nativeHeat076Init12_formula
    · exact nativeHeat076Init13_formula
    · exact nativeHeat076Init14_formula
    · exact nativeHeat076Init15_formula
    · exact nativeHeat076Init16_formula
    · exact nativeHeat076Init17_formula
    · exact nativeHeat076Init18_formula
    · exact nativeHeat076Init19_formula
    · exact nativeHeat076Init20_formula
theorem nativeHeatStep_hBase_076_Gen : nativeHeatBaseGen 76 = nativeHeat076Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_076_Gen, nativeHeatStep_hInit_076_Gen, nativeHeat076Base_formula]

theorem nativeHeatStep_hFixed_076_Gen : nativeHeatFixedGen 76 = nativeHeat076Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_076_Gen, nativeHeatStep_hFr_076_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat076Fixed01_formula
    · exact nativeHeat076Fixed02_formula
    · exact nativeHeat076Fixed03_formula
    · exact nativeHeat076Fixed04_formula
    · exact nativeHeat076Fixed05_formula
    · exact nativeHeat076Fixed06_formula
    · exact nativeHeat076Fixed07_formula
    · exact nativeHeat076Fixed08_formula
    · exact nativeHeat076Fixed09_formula
    · exact nativeHeat076Fixed10_formula
    · exact nativeHeat076Fixed11_formula
    · exact nativeHeat076Fixed12_formula
    · exact nativeHeat076Fixed13_formula
    · exact nativeHeat076Fixed14_formula
    · exact nativeHeat076Fixed15_formula
    · exact nativeHeat076Fixed16_formula
    · exact nativeHeat076Fixed17_formula
    · exact nativeHeat076Fixed18_formula
    · exact nativeHeat076Fixed19_formula
    · exact nativeHeat076Fixed20_formula

theorem nativeHeatStep_chk_076_Gen :
    nativeHeatPassRootsOk nativeGap077Old nativeHeat076Frames nativeHeat076Coef nativeHeat076Fixed nativeHeat076Base 48 nativeHeat076Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_076_Gen : NativeHeatStepPassNum 76 := by
  refine nativeHeatStepPassNum_of_literals 76 nativeGap077Old nativeHeat076Frames (nativeHeatExpArg nativeGap077Old)
    nativeHeat076Exp nativeHeat076Coef nativeHeat076Fixed nativeHeat076Init nativeHeat076Base nativeHeatStep_hOld_076_Gen
    nativeHeatStep_hFr_076_Gen nativeHeatStep_hArg_076_Gen nativeHeatStep_hExp_076_Gen
    nativeHeatStep_hCoef_076_Gen nativeHeatStep_hFixed_076_Gen
    nativeHeatStep_hInit_076_Gen nativeHeatStep_hBase_076_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_076_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_076_Gen :
    nativeHeatY0Gen 76 = nativeShiftedFrame 1 (min nativeGap077Old.x nativeGap077Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_076_Gen, nativeHeatStep_hInd_076_Gen]

theorem nativeHeatStepFrameNum_076_Gen : NativeHeatStepFrameNum 76 := by
  have h1 := nativeHeatStep_hOld_076_Gen
  have h2 := nativeHeatStep_hInd_076_Gen
  have h3 := nativeHeatStep_hVar_076_Gen
  have h4 := nativeHeatStep_hQm_076_Gen
  have h5 := nativeHeatStep_hQN_076_Gen
  have h6 := nativeHeatStep_hY0_076_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_076_Gen : NativeHeatStepIndivNum 76 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 76 (by norm_num)) = nativeGap077Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_076_Gen]; exact nativeGap077Old_source
  · rw [hc, nativeHeatStep_hInd_076_Gen]; exact nativeGap077Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_076_Gen : nativeHeatY48Gen 76 = nativeHeat076Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_076_Gen, nativeHeatStep_hFr_076_Gen,
    nativeHeatStep_hCoef_076_Gen, nativeHeatStep_hFixed_076_Gen,
    nativeHeatStep_hBase_076_Gen]
  exact nativeHeat076All48

theorem nativeHeatResultGen_076 : nativeHeatResultGen 76 = nativeHeat076Result := by
  rw [← nativeHeat076Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_076_Gen, nativeHeatStep_hY0_076_Gen, nativeHeatStep_hExp_076_Gen,
    nativeHeatStep_hInit_076_Gen, nativeHeatStep_hFixed_076_Gen]

end ASDExplicitGamma.Native

end
