module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat080Complete
public import ASDExplicitGamma.Numerics.Native.Gap081Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_080_Gen : nativeHeatOldRowGen 80 = nativeGap081Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_080_Gen : nativeHeatIndividualGen 80 = nativeGap081Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_080_Gen : nativeHeatGenVariance 80 = nativeHeat080Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_080_Gen, nativeHeat080Variance_formula]

theorem nativeHeatStep_hSpec_080_Gen : nativeHeatGenSpectral 80 = nativeHeat080Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_080_Gen, nativeHeat080Variance_formula]

theorem nativeHeatStep_hQm_080_Gen : nativeHeatGenQm 80 = nativeHeat080Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_080_Gen, nativeHeatStep_hSpec_080_Gen,
    nativeHeat080Qm_formula]

theorem nativeHeatStep_hQN_080_Gen : nativeHeatQNGen 80 = nativeHeat080QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_080_Gen, nativeHeat080QN_formula]

theorem nativeHeatStep_hFr_080_Gen : nativeHeatFramesGen 80 = nativeHeat080Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_080_Gen, nativeHeatStep_hInd_080_Gen,
    nativeHeatStep_hVar_080_Gen, nativeHeatStep_hQN_080_Gen, nativeHeat080Frames_formula]

theorem nativeHeatStep_hArg_080_Gen : nativeHeatExpArgGen 80 = nativeHeatExpArg nativeGap081Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_080_Gen]

theorem nativeHeatStep_hExp_080_Gen : nativeHeatExpGen 80 = nativeHeat080Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_080_Gen, nativeHeat080Exp_formula]

theorem nativeHeatStep_hCoef_080_Gen : nativeHeatCoefGen 80 = nativeHeat080Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_080_Gen, nativeHeat080Coef_formula]

theorem nativeHeatStep_hInit_080_Gen : nativeHeatInitGen 80 = nativeHeat080Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_080_Gen, nativeHeatStep_hVar_080_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat080Init00_formula
    · exact nativeHeat080Init01_formula
    · exact nativeHeat080Init02_formula
    · exact nativeHeat080Init03_formula
    · exact nativeHeat080Init04_formula
    · exact nativeHeat080Init05_formula
    · exact nativeHeat080Init06_formula
    · exact nativeHeat080Init07_formula
    · exact nativeHeat080Init08_formula
    · exact nativeHeat080Init09_formula
    · exact nativeHeat080Init10_formula
    · exact nativeHeat080Init11_formula
    · exact nativeHeat080Init12_formula
    · exact nativeHeat080Init13_formula
    · exact nativeHeat080Init14_formula
    · exact nativeHeat080Init15_formula
    · exact nativeHeat080Init16_formula
    · exact nativeHeat080Init17_formula
    · exact nativeHeat080Init18_formula
    · exact nativeHeat080Init19_formula
    · exact nativeHeat080Init20_formula
theorem nativeHeatStep_hBase_080_Gen : nativeHeatBaseGen 80 = nativeHeat080Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_080_Gen, nativeHeatStep_hInit_080_Gen, nativeHeat080Base_formula]

theorem nativeHeatStep_hFixed_080_Gen : nativeHeatFixedGen 80 = nativeHeat080Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_080_Gen, nativeHeatStep_hFr_080_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat080Fixed01_formula
    · exact nativeHeat080Fixed02_formula
    · exact nativeHeat080Fixed03_formula
    · exact nativeHeat080Fixed04_formula
    · exact nativeHeat080Fixed05_formula
    · exact nativeHeat080Fixed06_formula
    · exact nativeHeat080Fixed07_formula
    · exact nativeHeat080Fixed08_formula
    · exact nativeHeat080Fixed09_formula
    · exact nativeHeat080Fixed10_formula
    · exact nativeHeat080Fixed11_formula
    · exact nativeHeat080Fixed12_formula
    · exact nativeHeat080Fixed13_formula
    · exact nativeHeat080Fixed14_formula
    · exact nativeHeat080Fixed15_formula
    · exact nativeHeat080Fixed16_formula
    · exact nativeHeat080Fixed17_formula
    · exact nativeHeat080Fixed18_formula
    · exact nativeHeat080Fixed19_formula
    · exact nativeHeat080Fixed20_formula

theorem nativeHeatStep_chk_080_Gen :
    nativeHeatPassRootsOk nativeGap081Old nativeHeat080Frames nativeHeat080Coef nativeHeat080Fixed nativeHeat080Base 48 nativeHeat080Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_080_Gen : NativeHeatStepPassNum 80 := by
  refine nativeHeatStepPassNum_of_literals 80 nativeGap081Old nativeHeat080Frames (nativeHeatExpArg nativeGap081Old)
    nativeHeat080Exp nativeHeat080Coef nativeHeat080Fixed nativeHeat080Init nativeHeat080Base nativeHeatStep_hOld_080_Gen
    nativeHeatStep_hFr_080_Gen nativeHeatStep_hArg_080_Gen nativeHeatStep_hExp_080_Gen
    nativeHeatStep_hCoef_080_Gen nativeHeatStep_hFixed_080_Gen
    nativeHeatStep_hInit_080_Gen nativeHeatStep_hBase_080_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_080_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_080_Gen :
    nativeHeatY0Gen 80 = nativeShiftedFrame 1 (min nativeGap081Old.x nativeGap081Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_080_Gen, nativeHeatStep_hInd_080_Gen]

theorem nativeHeatStepFrameNum_080_Gen : NativeHeatStepFrameNum 80 := by
  have h1 := nativeHeatStep_hOld_080_Gen
  have h2 := nativeHeatStep_hInd_080_Gen
  have h3 := nativeHeatStep_hVar_080_Gen
  have h4 := nativeHeatStep_hQm_080_Gen
  have h5 := nativeHeatStep_hQN_080_Gen
  have h6 := nativeHeatStep_hY0_080_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_080_Gen : NativeHeatStepIndivNum 80 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 80 (by norm_num)) = nativeGap081Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_080_Gen]; exact nativeGap081Old_source
  · rw [hc, nativeHeatStep_hInd_080_Gen]; exact nativeGap081Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_080_Gen : nativeHeatY48Gen 80 = nativeHeat080Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_080_Gen, nativeHeatStep_hFr_080_Gen,
    nativeHeatStep_hCoef_080_Gen, nativeHeatStep_hFixed_080_Gen,
    nativeHeatStep_hBase_080_Gen]
  exact nativeHeat080All48

theorem nativeHeatResultGen_080 : nativeHeatResultGen 80 = nativeHeat080Result := by
  rw [← nativeHeat080Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_080_Gen, nativeHeatStep_hY0_080_Gen, nativeHeatStep_hExp_080_Gen,
    nativeHeatStep_hInit_080_Gen, nativeHeatStep_hFixed_080_Gen]

end ASDExplicitGamma.Native

end
