module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat064Complete
public import ASDExplicitGamma.Numerics.Native.Gap065Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_064_Gen : nativeHeatOldRowGen 64 = nativeGap065Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_064_Gen : nativeHeatIndividualGen 64 = nativeGap065Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_064_Gen : nativeHeatGenVariance 64 = nativeHeat064Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_064_Gen, nativeHeat064Variance_formula]

theorem nativeHeatStep_hSpec_064_Gen : nativeHeatGenSpectral 64 = nativeHeat064Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_064_Gen, nativeHeat064Variance_formula]

theorem nativeHeatStep_hQm_064_Gen : nativeHeatGenQm 64 = nativeHeat064Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_064_Gen, nativeHeatStep_hSpec_064_Gen,
    nativeHeat064Qm_formula]

theorem nativeHeatStep_hQN_064_Gen : nativeHeatQNGen 64 = nativeHeat064QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_064_Gen, nativeHeat064QN_formula]

theorem nativeHeatStep_hFr_064_Gen : nativeHeatFramesGen 64 = nativeHeat064Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_064_Gen, nativeHeatStep_hInd_064_Gen,
    nativeHeatStep_hVar_064_Gen, nativeHeatStep_hQN_064_Gen, nativeHeat064Frames_formula]

theorem nativeHeatStep_hArg_064_Gen : nativeHeatExpArgGen 64 = nativeHeatExpArg nativeGap065Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_064_Gen]

theorem nativeHeatStep_hExp_064_Gen : nativeHeatExpGen 64 = nativeHeat064Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_064_Gen, nativeHeat064Exp_formula]

theorem nativeHeatStep_hCoef_064_Gen : nativeHeatCoefGen 64 = nativeHeat064Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_064_Gen, nativeHeat064Coef_formula]

theorem nativeHeatStep_hInit_064_Gen : nativeHeatInitGen 64 = nativeHeat064Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_064_Gen, nativeHeatStep_hVar_064_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat064Init00_formula
    · exact nativeHeat064Init01_formula
    · exact nativeHeat064Init02_formula
    · exact nativeHeat064Init03_formula
    · exact nativeHeat064Init04_formula
    · exact nativeHeat064Init05_formula
    · exact nativeHeat064Init06_formula
    · exact nativeHeat064Init07_formula
    · exact nativeHeat064Init08_formula
    · exact nativeHeat064Init09_formula
    · exact nativeHeat064Init10_formula
    · exact nativeHeat064Init11_formula
    · exact nativeHeat064Init12_formula
    · exact nativeHeat064Init13_formula
    · exact nativeHeat064Init14_formula
    · exact nativeHeat064Init15_formula
    · exact nativeHeat064Init16_formula
    · exact nativeHeat064Init17_formula
    · exact nativeHeat064Init18_formula
    · exact nativeHeat064Init19_formula
    · exact nativeHeat064Init20_formula
theorem nativeHeatStep_hBase_064_Gen : nativeHeatBaseGen 64 = nativeHeat064Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_064_Gen, nativeHeatStep_hInit_064_Gen, nativeHeat064Base_formula]

theorem nativeHeatStep_hFixed_064_Gen : nativeHeatFixedGen 64 = nativeHeat064Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_064_Gen, nativeHeatStep_hFr_064_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat064Fixed01_formula
    · exact nativeHeat064Fixed02_formula
    · exact nativeHeat064Fixed03_formula
    · exact nativeHeat064Fixed04_formula
    · exact nativeHeat064Fixed05_formula
    · exact nativeHeat064Fixed06_formula
    · exact nativeHeat064Fixed07_formula
    · exact nativeHeat064Fixed08_formula
    · exact nativeHeat064Fixed09_formula
    · exact nativeHeat064Fixed10_formula
    · exact nativeHeat064Fixed11_formula
    · exact nativeHeat064Fixed12_formula
    · exact nativeHeat064Fixed13_formula
    · exact nativeHeat064Fixed14_formula
    · exact nativeHeat064Fixed15_formula
    · exact nativeHeat064Fixed16_formula
    · exact nativeHeat064Fixed17_formula
    · exact nativeHeat064Fixed18_formula
    · exact nativeHeat064Fixed19_formula
    · exact nativeHeat064Fixed20_formula

theorem nativeHeatStep_chk_064_Gen :
    nativeHeatPassRootsOk nativeGap065Old nativeHeat064Frames nativeHeat064Coef nativeHeat064Fixed nativeHeat064Base 48 nativeHeat064Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_064_Gen : NativeHeatStepPassNum 64 := by
  refine nativeHeatStepPassNum_of_literals 64 nativeGap065Old nativeHeat064Frames (nativeHeatExpArg nativeGap065Old)
    nativeHeat064Exp nativeHeat064Coef nativeHeat064Fixed nativeHeat064Init nativeHeat064Base nativeHeatStep_hOld_064_Gen
    nativeHeatStep_hFr_064_Gen nativeHeatStep_hArg_064_Gen nativeHeatStep_hExp_064_Gen
    nativeHeatStep_hCoef_064_Gen nativeHeatStep_hFixed_064_Gen
    nativeHeatStep_hInit_064_Gen nativeHeatStep_hBase_064_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_064_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_064_Gen :
    nativeHeatY0Gen 64 = nativeShiftedFrame 1 (min nativeGap065Old.x nativeGap065Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_064_Gen, nativeHeatStep_hInd_064_Gen]

theorem nativeHeatStepFrameNum_064_Gen : NativeHeatStepFrameNum 64 := by
  have h1 := nativeHeatStep_hOld_064_Gen
  have h2 := nativeHeatStep_hInd_064_Gen
  have h3 := nativeHeatStep_hVar_064_Gen
  have h4 := nativeHeatStep_hQm_064_Gen
  have h5 := nativeHeatStep_hQN_064_Gen
  have h6 := nativeHeatStep_hY0_064_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_064_Gen : NativeHeatStepIndivNum 64 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 64 (by norm_num)) = nativeGap065Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_064_Gen]; exact nativeGap065Old_source
  · rw [hc, nativeHeatStep_hInd_064_Gen]; exact nativeGap065Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_064_Gen : nativeHeatY48Gen 64 = nativeHeat064Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_064_Gen, nativeHeatStep_hFr_064_Gen,
    nativeHeatStep_hCoef_064_Gen, nativeHeatStep_hFixed_064_Gen,
    nativeHeatStep_hBase_064_Gen]
  exact nativeHeat064All48

theorem nativeHeatResultGen_064 : nativeHeatResultGen 64 = nativeHeat064Result := by
  rw [← nativeHeat064Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_064_Gen, nativeHeatStep_hY0_064_Gen, nativeHeatStep_hExp_064_Gen,
    nativeHeatStep_hInit_064_Gen, nativeHeatStep_hFixed_064_Gen]

end ASDExplicitGamma.Native

end
