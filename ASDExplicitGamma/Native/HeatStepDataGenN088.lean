module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat088Complete
public import ASDExplicitGamma.Numerics.Native.Gap089Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_088_Gen : nativeHeatOldRowGen 88 = nativeGap089Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_088_Gen : nativeHeatIndividualGen 88 = nativeGap089Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_088_Gen : nativeHeatGenVariance 88 = nativeHeat088Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_088_Gen, nativeHeat088Variance_formula]

theorem nativeHeatStep_hSpec_088_Gen : nativeHeatGenSpectral 88 = nativeHeat088Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_088_Gen, nativeHeat088Variance_formula]

theorem nativeHeatStep_hQm_088_Gen : nativeHeatGenQm 88 = nativeHeat088Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_088_Gen, nativeHeatStep_hSpec_088_Gen,
    nativeHeat088Qm_formula]

theorem nativeHeatStep_hQN_088_Gen : nativeHeatQNGen 88 = nativeHeat088QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_088_Gen, nativeHeat088QN_formula]

theorem nativeHeatStep_hFr_088_Gen : nativeHeatFramesGen 88 = nativeHeat088Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_088_Gen, nativeHeatStep_hInd_088_Gen,
    nativeHeatStep_hVar_088_Gen, nativeHeatStep_hQN_088_Gen, nativeHeat088Frames_formula]

theorem nativeHeatStep_hArg_088_Gen : nativeHeatExpArgGen 88 = nativeHeatExpArg nativeGap089Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_088_Gen]

theorem nativeHeatStep_hExp_088_Gen : nativeHeatExpGen 88 = nativeHeat088Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_088_Gen, nativeHeat088Exp_formula]

theorem nativeHeatStep_hCoef_088_Gen : nativeHeatCoefGen 88 = nativeHeat088Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_088_Gen, nativeHeat088Coef_formula]

theorem nativeHeatStep_hInit_088_Gen : nativeHeatInitGen 88 = nativeHeat088Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_088_Gen, nativeHeatStep_hVar_088_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat088Init00_formula
    · exact nativeHeat088Init01_formula
    · exact nativeHeat088Init02_formula
    · exact nativeHeat088Init03_formula
    · exact nativeHeat088Init04_formula
    · exact nativeHeat088Init05_formula
    · exact nativeHeat088Init06_formula
    · exact nativeHeat088Init07_formula
    · exact nativeHeat088Init08_formula
    · exact nativeHeat088Init09_formula
    · exact nativeHeat088Init10_formula
    · exact nativeHeat088Init11_formula
    · exact nativeHeat088Init12_formula
    · exact nativeHeat088Init13_formula
    · exact nativeHeat088Init14_formula
    · exact nativeHeat088Init15_formula
    · exact nativeHeat088Init16_formula
    · exact nativeHeat088Init17_formula
    · exact nativeHeat088Init18_formula
    · exact nativeHeat088Init19_formula
    · exact nativeHeat088Init20_formula
theorem nativeHeatStep_hBase_088_Gen : nativeHeatBaseGen 88 = nativeHeat088Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_088_Gen, nativeHeatStep_hInit_088_Gen, nativeHeat088Base_formula]

theorem nativeHeatStep_hFixed_088_Gen : nativeHeatFixedGen 88 = nativeHeat088Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_088_Gen, nativeHeatStep_hFr_088_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat088Fixed01_formula
    · exact nativeHeat088Fixed02_formula
    · exact nativeHeat088Fixed03_formula
    · exact nativeHeat088Fixed04_formula
    · exact nativeHeat088Fixed05_formula
    · exact nativeHeat088Fixed06_formula
    · exact nativeHeat088Fixed07_formula
    · exact nativeHeat088Fixed08_formula
    · exact nativeHeat088Fixed09_formula
    · exact nativeHeat088Fixed10_formula
    · exact nativeHeat088Fixed11_formula
    · exact nativeHeat088Fixed12_formula
    · exact nativeHeat088Fixed13_formula
    · exact nativeHeat088Fixed14_formula
    · exact nativeHeat088Fixed15_formula
    · exact nativeHeat088Fixed16_formula
    · exact nativeHeat088Fixed17_formula
    · exact nativeHeat088Fixed18_formula
    · exact nativeHeat088Fixed19_formula
    · exact nativeHeat088Fixed20_formula

theorem nativeHeatStep_chk_088_Gen :
    nativeHeatPassRootsOk nativeGap089Old nativeHeat088Frames nativeHeat088Coef nativeHeat088Fixed nativeHeat088Base 48 nativeHeat088Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_088_Gen : NativeHeatStepPassNum 88 := by
  refine nativeHeatStepPassNum_of_literals 88 nativeGap089Old nativeHeat088Frames (nativeHeatExpArg nativeGap089Old)
    nativeHeat088Exp nativeHeat088Coef nativeHeat088Fixed nativeHeat088Init nativeHeat088Base nativeHeatStep_hOld_088_Gen
    nativeHeatStep_hFr_088_Gen nativeHeatStep_hArg_088_Gen nativeHeatStep_hExp_088_Gen
    nativeHeatStep_hCoef_088_Gen nativeHeatStep_hFixed_088_Gen
    nativeHeatStep_hInit_088_Gen nativeHeatStep_hBase_088_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_088_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_088_Gen :
    nativeHeatY0Gen 88 = nativeShiftedFrame 1 (min nativeGap089Old.x nativeGap089Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_088_Gen, nativeHeatStep_hInd_088_Gen]

theorem nativeHeatStepFrameNum_088_Gen : NativeHeatStepFrameNum 88 := by
  have h1 := nativeHeatStep_hOld_088_Gen
  have h2 := nativeHeatStep_hInd_088_Gen
  have h3 := nativeHeatStep_hVar_088_Gen
  have h4 := nativeHeatStep_hQm_088_Gen
  have h5 := nativeHeatStep_hQN_088_Gen
  have h6 := nativeHeatStep_hY0_088_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_088_Gen : NativeHeatStepIndivNum 88 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 88 (by norm_num)) = nativeGap089Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_088_Gen]; exact nativeGap089Old_source
  · rw [hc, nativeHeatStep_hInd_088_Gen]; exact nativeGap089Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_088_Gen : nativeHeatY48Gen 88 = nativeHeat088Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_088_Gen, nativeHeatStep_hFr_088_Gen,
    nativeHeatStep_hCoef_088_Gen, nativeHeatStep_hFixed_088_Gen,
    nativeHeatStep_hBase_088_Gen]
  exact nativeHeat088All48

theorem nativeHeatResultGen_088 : nativeHeatResultGen 88 = nativeHeat088Result := by
  rw [← nativeHeat088Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_088_Gen, nativeHeatStep_hY0_088_Gen, nativeHeatStep_hExp_088_Gen,
    nativeHeatStep_hInit_088_Gen, nativeHeatStep_hFixed_088_Gen]

end ASDExplicitGamma.Native

end
