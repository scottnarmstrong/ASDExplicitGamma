module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat057Complete
public import ASDExplicitGamma.Numerics.Native.Gap058Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_057_Gen : nativeHeatOldRowGen 57 = nativeGap058Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_057_Gen : nativeHeatIndividualGen 57 = nativeGap058Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_057_Gen : nativeHeatGenVariance 57 = nativeHeat057Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_057_Gen, nativeHeat057Variance_formula]

theorem nativeHeatStep_hSpec_057_Gen : nativeHeatGenSpectral 57 = nativeHeat057Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_057_Gen, nativeHeat057Variance_formula]

theorem nativeHeatStep_hQm_057_Gen : nativeHeatGenQm 57 = nativeHeat057Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_057_Gen, nativeHeatStep_hSpec_057_Gen,
    nativeHeat057Qm_formula]

theorem nativeHeatStep_hQN_057_Gen : nativeHeatQNGen 57 = nativeHeat057QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_057_Gen, nativeHeat057QN_formula]

theorem nativeHeatStep_hFr_057_Gen : nativeHeatFramesGen 57 = nativeHeat057Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_057_Gen, nativeHeatStep_hInd_057_Gen,
    nativeHeatStep_hVar_057_Gen, nativeHeatStep_hQN_057_Gen, nativeHeat057Frames_formula]

theorem nativeHeatStep_hArg_057_Gen : nativeHeatExpArgGen 57 = nativeHeatExpArg nativeGap058Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_057_Gen]

theorem nativeHeatStep_hExp_057_Gen : nativeHeatExpGen 57 = nativeHeat057Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_057_Gen, nativeHeat057Exp_formula]

theorem nativeHeatStep_hCoef_057_Gen : nativeHeatCoefGen 57 = nativeHeat057Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_057_Gen, nativeHeat057Coef_formula]

theorem nativeHeatStep_hInit_057_Gen : nativeHeatInitGen 57 = nativeHeat057Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_057_Gen, nativeHeatStep_hVar_057_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat057Init00_formula
    · exact nativeHeat057Init01_formula
    · exact nativeHeat057Init02_formula
    · exact nativeHeat057Init03_formula
    · exact nativeHeat057Init04_formula
    · exact nativeHeat057Init05_formula
    · exact nativeHeat057Init06_formula
    · exact nativeHeat057Init07_formula
    · exact nativeHeat057Init08_formula
    · exact nativeHeat057Init09_formula
    · exact nativeHeat057Init10_formula
    · exact nativeHeat057Init11_formula
    · exact nativeHeat057Init12_formula
    · exact nativeHeat057Init13_formula
    · exact nativeHeat057Init14_formula
    · exact nativeHeat057Init15_formula
    · exact nativeHeat057Init16_formula
    · exact nativeHeat057Init17_formula
    · exact nativeHeat057Init18_formula
    · exact nativeHeat057Init19_formula
    · exact nativeHeat057Init20_formula
theorem nativeHeatStep_hBase_057_Gen : nativeHeatBaseGen 57 = nativeHeat057Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_057_Gen, nativeHeatStep_hInit_057_Gen, nativeHeat057Base_formula]

theorem nativeHeatStep_hFixed_057_Gen : nativeHeatFixedGen 57 = nativeHeat057Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_057_Gen, nativeHeatStep_hFr_057_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat057Fixed01_formula
    · exact nativeHeat057Fixed02_formula
    · exact nativeHeat057Fixed03_formula
    · exact nativeHeat057Fixed04_formula
    · exact nativeHeat057Fixed05_formula
    · exact nativeHeat057Fixed06_formula
    · exact nativeHeat057Fixed07_formula
    · exact nativeHeat057Fixed08_formula
    · exact nativeHeat057Fixed09_formula
    · exact nativeHeat057Fixed10_formula
    · exact nativeHeat057Fixed11_formula
    · exact nativeHeat057Fixed12_formula
    · exact nativeHeat057Fixed13_formula
    · exact nativeHeat057Fixed14_formula
    · exact nativeHeat057Fixed15_formula
    · exact nativeHeat057Fixed16_formula
    · exact nativeHeat057Fixed17_formula
    · exact nativeHeat057Fixed18_formula
    · exact nativeHeat057Fixed19_formula
    · exact nativeHeat057Fixed20_formula

theorem nativeHeatStep_chk_057_Gen :
    nativeHeatPassRootsOk nativeGap058Old nativeHeat057Frames nativeHeat057Coef nativeHeat057Fixed nativeHeat057Base 48 nativeHeat057Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_057_Gen : NativeHeatStepPassNum 57 := by
  refine nativeHeatStepPassNum_of_literals 57 nativeGap058Old nativeHeat057Frames (nativeHeatExpArg nativeGap058Old)
    nativeHeat057Exp nativeHeat057Coef nativeHeat057Fixed nativeHeat057Init nativeHeat057Base nativeHeatStep_hOld_057_Gen
    nativeHeatStep_hFr_057_Gen nativeHeatStep_hArg_057_Gen nativeHeatStep_hExp_057_Gen
    nativeHeatStep_hCoef_057_Gen nativeHeatStep_hFixed_057_Gen
    nativeHeatStep_hInit_057_Gen nativeHeatStep_hBase_057_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_057_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_057_Gen :
    nativeHeatY0Gen 57 = nativeShiftedFrame 1 (min nativeGap058Old.x nativeGap058Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_057_Gen, nativeHeatStep_hInd_057_Gen]

theorem nativeHeatStepFrameNum_057_Gen : NativeHeatStepFrameNum 57 := by
  have h1 := nativeHeatStep_hOld_057_Gen
  have h2 := nativeHeatStep_hInd_057_Gen
  have h3 := nativeHeatStep_hVar_057_Gen
  have h4 := nativeHeatStep_hQm_057_Gen
  have h5 := nativeHeatStep_hQN_057_Gen
  have h6 := nativeHeatStep_hY0_057_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_057_Gen : NativeHeatStepIndivNum 57 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 57 (by norm_num)) = nativeGap058Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_057_Gen]; exact nativeGap058Old_source
  · rw [hc, nativeHeatStep_hInd_057_Gen]; exact nativeGap058Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_057_Gen : nativeHeatY48Gen 57 = nativeHeat057Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_057_Gen, nativeHeatStep_hFr_057_Gen,
    nativeHeatStep_hCoef_057_Gen, nativeHeatStep_hFixed_057_Gen,
    nativeHeatStep_hBase_057_Gen]
  exact nativeHeat057All48

theorem nativeHeatResultGen_057 : nativeHeatResultGen 57 = nativeHeat057Result := by
  rw [← nativeHeat057Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_057_Gen, nativeHeatStep_hY0_057_Gen, nativeHeatStep_hExp_057_Gen,
    nativeHeatStep_hInit_057_Gen, nativeHeatStep_hFixed_057_Gen]

end ASDExplicitGamma.Native

end
