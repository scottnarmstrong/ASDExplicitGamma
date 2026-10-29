module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat020Complete
public import ASDExplicitGamma.Numerics.Native.Gap021Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_020_Gen : nativeHeatOldRowGen 20 = nativeGap021Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_020_Gen : nativeHeatIndividualGen 20 = nativeGap021Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_020_Gen : nativeHeatGenVariance 20 = nativeHeat020Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_020_Gen, nativeHeat020Variance_formula]

theorem nativeHeatStep_hSpec_020_Gen : nativeHeatGenSpectral 20 = nativeHeat020Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_020_Gen, nativeHeat020Variance_formula]

theorem nativeHeatStep_hQm_020_Gen : nativeHeatGenQm 20 = nativeHeat020Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_020_Gen, nativeHeatStep_hSpec_020_Gen,
    nativeHeat020Qm_formula]

theorem nativeHeatStep_hQN_020_Gen : nativeHeatQNGen 20 = nativeHeat020QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_020_Gen, nativeHeat020QN_formula]

theorem nativeHeatStep_hFr_020_Gen : nativeHeatFramesGen 20 = nativeHeat020Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_020_Gen, nativeHeatStep_hInd_020_Gen,
    nativeHeatStep_hVar_020_Gen, nativeHeatStep_hQN_020_Gen, nativeHeat020Frames_formula]

theorem nativeHeatStep_hArg_020_Gen : nativeHeatExpArgGen 20 = nativeHeatExpArg nativeGap021Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_020_Gen]

theorem nativeHeatStep_hExp_020_Gen : nativeHeatExpGen 20 = nativeHeat020Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_020_Gen, nativeHeat020Exp_formula]

theorem nativeHeatStep_hCoef_020_Gen : nativeHeatCoefGen 20 = nativeHeat020Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_020_Gen, nativeHeat020Coef_formula]

theorem nativeHeatStep_hInit_020_Gen : nativeHeatInitGen 20 = nativeHeat020Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_020_Gen, nativeHeatStep_hVar_020_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat020Init00_formula
    · exact nativeHeat020Init01_formula
    · exact nativeHeat020Init02_formula
    · exact nativeHeat020Init03_formula
    · exact nativeHeat020Init04_formula
    · exact nativeHeat020Init05_formula
    · exact nativeHeat020Init06_formula
    · exact nativeHeat020Init07_formula
    · exact nativeHeat020Init08_formula
    · exact nativeHeat020Init09_formula
    · exact nativeHeat020Init10_formula
    · exact nativeHeat020Init11_formula
    · exact nativeHeat020Init12_formula
    · exact nativeHeat020Init13_formula
    · exact nativeHeat020Init14_formula
    · exact nativeHeat020Init15_formula
    · exact nativeHeat020Init16_formula
    · exact nativeHeat020Init17_formula
    · exact nativeHeat020Init18_formula
    · exact nativeHeat020Init19_formula
    · exact nativeHeat020Init20_formula
theorem nativeHeatStep_hBase_020_Gen : nativeHeatBaseGen 20 = nativeHeat020Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_020_Gen, nativeHeatStep_hInit_020_Gen, nativeHeat020Base_formula]

theorem nativeHeatStep_hFixed_020_Gen : nativeHeatFixedGen 20 = nativeHeat020Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_020_Gen, nativeHeatStep_hFr_020_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat020Fixed01_formula
    · exact nativeHeat020Fixed02_formula
    · exact nativeHeat020Fixed03_formula
    · exact nativeHeat020Fixed04_formula
    · exact nativeHeat020Fixed05_formula
    · exact nativeHeat020Fixed06_formula
    · exact nativeHeat020Fixed07_formula
    · exact nativeHeat020Fixed08_formula
    · exact nativeHeat020Fixed09_formula
    · exact nativeHeat020Fixed10_formula
    · exact nativeHeat020Fixed11_formula
    · exact nativeHeat020Fixed12_formula
    · exact nativeHeat020Fixed13_formula
    · exact nativeHeat020Fixed14_formula
    · exact nativeHeat020Fixed15_formula
    · exact nativeHeat020Fixed16_formula
    · exact nativeHeat020Fixed17_formula
    · exact nativeHeat020Fixed18_formula
    · exact nativeHeat020Fixed19_formula
    · exact nativeHeat020Fixed20_formula

theorem nativeHeatStep_chk_020_Gen :
    nativeHeatPassRootsOk nativeGap021Old nativeHeat020Frames nativeHeat020Coef nativeHeat020Fixed nativeHeat020Base 48 nativeHeat020Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_020_Gen : NativeHeatStepPassNum 20 := by
  refine nativeHeatStepPassNum_of_literals 20 nativeGap021Old nativeHeat020Frames (nativeHeatExpArg nativeGap021Old)
    nativeHeat020Exp nativeHeat020Coef nativeHeat020Fixed nativeHeat020Init nativeHeat020Base nativeHeatStep_hOld_020_Gen
    nativeHeatStep_hFr_020_Gen nativeHeatStep_hArg_020_Gen nativeHeatStep_hExp_020_Gen
    nativeHeatStep_hCoef_020_Gen nativeHeatStep_hFixed_020_Gen
    nativeHeatStep_hInit_020_Gen nativeHeatStep_hBase_020_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_020_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_020_Gen :
    nativeHeatY0Gen 20 = nativeShiftedFrame 1 (min nativeGap021Old.x nativeGap021Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_020_Gen, nativeHeatStep_hInd_020_Gen]

theorem nativeHeatStepFrameNum_020_Gen : NativeHeatStepFrameNum 20 := by
  have h1 := nativeHeatStep_hOld_020_Gen
  have h2 := nativeHeatStep_hInd_020_Gen
  have h3 := nativeHeatStep_hVar_020_Gen
  have h4 := nativeHeatStep_hQm_020_Gen
  have h5 := nativeHeatStep_hQN_020_Gen
  have h6 := nativeHeatStep_hY0_020_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_020_Gen : NativeHeatStepIndivNum 20 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 20 (by norm_num)) = nativeGap021Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_020_Gen]; exact nativeGap021Old_source
  · rw [hc, nativeHeatStep_hInd_020_Gen]; exact nativeGap021Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_020_Gen : nativeHeatY48Gen 20 = nativeHeat020Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_020_Gen, nativeHeatStep_hFr_020_Gen,
    nativeHeatStep_hCoef_020_Gen, nativeHeatStep_hFixed_020_Gen,
    nativeHeatStep_hBase_020_Gen]
  exact nativeHeat020All48

theorem nativeHeatResultGen_020 : nativeHeatResultGen 20 = nativeHeat020Result := by
  rw [← nativeHeat020Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_020_Gen, nativeHeatStep_hY0_020_Gen, nativeHeatStep_hExp_020_Gen,
    nativeHeatStep_hInit_020_Gen, nativeHeatStep_hFixed_020_Gen]

end ASDExplicitGamma.Native

end
