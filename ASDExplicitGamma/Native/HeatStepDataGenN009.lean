module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat009Complete
public import ASDExplicitGamma.Numerics.Native.Gap010Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_009_Gen : nativeHeatOldRowGen 9 = nativeGap010Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_009_Gen : nativeHeatIndividualGen 9 = nativeGap010Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_009_Gen : nativeHeatGenVariance 9 = nativeHeat009Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_009_Gen, nativeHeat009Variance_formula]

theorem nativeHeatStep_hSpec_009_Gen : nativeHeatGenSpectral 9 = nativeHeat009Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_009_Gen, nativeHeat009Variance_formula]

theorem nativeHeatStep_hQm_009_Gen : nativeHeatGenQm 9 = nativeHeat009Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_009_Gen, nativeHeatStep_hSpec_009_Gen,
    nativeHeat009Qm_formula]

theorem nativeHeatStep_hQN_009_Gen : nativeHeatQNGen 9 = nativeHeat009QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_009_Gen, nativeHeat009QN_formula]

theorem nativeHeatStep_hFr_009_Gen : nativeHeatFramesGen 9 = nativeHeat009Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_009_Gen, nativeHeatStep_hInd_009_Gen,
    nativeHeatStep_hVar_009_Gen, nativeHeatStep_hQN_009_Gen, nativeHeat009Frames_formula]

theorem nativeHeatStep_hArg_009_Gen : nativeHeatExpArgGen 9 = nativeHeatExpArg nativeGap010Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_009_Gen]

theorem nativeHeatStep_hExp_009_Gen : nativeHeatExpGen 9 = nativeHeat009Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_009_Gen, nativeHeat009Exp_formula]

theorem nativeHeatStep_hCoef_009_Gen : nativeHeatCoefGen 9 = nativeHeat009Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_009_Gen, nativeHeat009Coef_formula]

theorem nativeHeatStep_hInit_009_Gen : nativeHeatInitGen 9 = nativeHeat009Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_009_Gen, nativeHeatStep_hVar_009_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat009Init00_formula
    · exact nativeHeat009Init01_formula
    · exact nativeHeat009Init02_formula
    · exact nativeHeat009Init03_formula
    · exact nativeHeat009Init04_formula
    · exact nativeHeat009Init05_formula
    · exact nativeHeat009Init06_formula
    · exact nativeHeat009Init07_formula
    · exact nativeHeat009Init08_formula
    · exact nativeHeat009Init09_formula
    · exact nativeHeat009Init10_formula
    · exact nativeHeat009Init11_formula
    · exact nativeHeat009Init12_formula
    · exact nativeHeat009Init13_formula
    · exact nativeHeat009Init14_formula
    · exact nativeHeat009Init15_formula
    · exact nativeHeat009Init16_formula
    · exact nativeHeat009Init17_formula
    · exact nativeHeat009Init18_formula
    · exact nativeHeat009Init19_formula
    · exact nativeHeat009Init20_formula
theorem nativeHeatStep_hBase_009_Gen : nativeHeatBaseGen 9 = nativeHeat009Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_009_Gen, nativeHeatStep_hInit_009_Gen, nativeHeat009Base_formula]

theorem nativeHeatStep_hFixed_009_Gen : nativeHeatFixedGen 9 = nativeHeat009Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_009_Gen, nativeHeatStep_hFr_009_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat009Fixed01_formula
    · exact nativeHeat009Fixed02_formula
    · exact nativeHeat009Fixed03_formula
    · exact nativeHeat009Fixed04_formula
    · exact nativeHeat009Fixed05_formula
    · exact nativeHeat009Fixed06_formula
    · exact nativeHeat009Fixed07_formula
    · exact nativeHeat009Fixed08_formula
    · exact nativeHeat009Fixed09_formula
    · exact nativeHeat009Fixed10_formula
    · exact nativeHeat009Fixed11_formula
    · exact nativeHeat009Fixed12_formula
    · exact nativeHeat009Fixed13_formula
    · exact nativeHeat009Fixed14_formula
    · exact nativeHeat009Fixed15_formula
    · exact nativeHeat009Fixed16_formula
    · exact nativeHeat009Fixed17_formula
    · exact nativeHeat009Fixed18_formula
    · exact nativeHeat009Fixed19_formula
    · exact nativeHeat009Fixed20_formula

theorem nativeHeatStep_chk_009_Gen :
    nativeHeatPassRootsOk nativeGap010Old nativeHeat009Frames nativeHeat009Coef nativeHeat009Fixed nativeHeat009Base 48 nativeHeat009Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_009_Gen : NativeHeatStepPassNum 9 := by
  refine nativeHeatStepPassNum_of_literals 9 nativeGap010Old nativeHeat009Frames (nativeHeatExpArg nativeGap010Old)
    nativeHeat009Exp nativeHeat009Coef nativeHeat009Fixed nativeHeat009Init nativeHeat009Base nativeHeatStep_hOld_009_Gen
    nativeHeatStep_hFr_009_Gen nativeHeatStep_hArg_009_Gen nativeHeatStep_hExp_009_Gen
    nativeHeatStep_hCoef_009_Gen nativeHeatStep_hFixed_009_Gen
    nativeHeatStep_hInit_009_Gen nativeHeatStep_hBase_009_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_009_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_009_Gen :
    nativeHeatY0Gen 9 = nativeShiftedFrame 1 (min nativeGap010Old.x nativeGap010Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_009_Gen, nativeHeatStep_hInd_009_Gen]

theorem nativeHeatStepFrameNum_009_Gen : NativeHeatStepFrameNum 9 := by
  have h1 := nativeHeatStep_hOld_009_Gen
  have h2 := nativeHeatStep_hInd_009_Gen
  have h3 := nativeHeatStep_hVar_009_Gen
  have h4 := nativeHeatStep_hQm_009_Gen
  have h5 := nativeHeatStep_hQN_009_Gen
  have h6 := nativeHeatStep_hY0_009_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_009_Gen : NativeHeatStepIndivNum 9 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 9 (by norm_num)) = nativeGap010Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_009_Gen]; exact nativeGap010Old_source
  · rw [hc, nativeHeatStep_hInd_009_Gen]; exact nativeGap010Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_009_Gen : nativeHeatY48Gen 9 = nativeHeat009Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_009_Gen, nativeHeatStep_hFr_009_Gen,
    nativeHeatStep_hCoef_009_Gen, nativeHeatStep_hFixed_009_Gen,
    nativeHeatStep_hBase_009_Gen]
  exact nativeHeat009All48

theorem nativeHeatResultGen_009 : nativeHeatResultGen 9 = nativeHeat009Result := by
  rw [← nativeHeat009Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_009_Gen, nativeHeatStep_hY0_009_Gen, nativeHeatStep_hExp_009_Gen,
    nativeHeatStep_hInit_009_Gen, nativeHeatStep_hFixed_009_Gen]

end ASDExplicitGamma.Native

end
