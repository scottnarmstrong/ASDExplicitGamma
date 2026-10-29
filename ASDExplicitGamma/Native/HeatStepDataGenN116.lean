module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat116Complete
public import ASDExplicitGamma.Numerics.Native.Gap117Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_116_Gen : nativeHeatOldRowGen 116 = nativeGap117Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_116_Gen : nativeHeatIndividualGen 116 = nativeGap117Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_116_Gen : nativeHeatGenVariance 116 = nativeHeat116Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_116_Gen, nativeHeat116Variance_formula]

theorem nativeHeatStep_hSpec_116_Gen : nativeHeatGenSpectral 116 = nativeHeat116Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_116_Gen, nativeHeat116Variance_formula]

theorem nativeHeatStep_hQm_116_Gen : nativeHeatGenQm 116 = nativeHeat116Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_116_Gen, nativeHeatStep_hSpec_116_Gen,
    nativeHeat116Qm_formula]

theorem nativeHeatStep_hQN_116_Gen : nativeHeatQNGen 116 = nativeHeat116QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_116_Gen, nativeHeat116QN_formula]

theorem nativeHeatStep_hFr_116_Gen : nativeHeatFramesGen 116 = nativeHeat116Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_116_Gen, nativeHeatStep_hInd_116_Gen,
    nativeHeatStep_hVar_116_Gen, nativeHeatStep_hQN_116_Gen, nativeHeat116Frames_formula]

theorem nativeHeatStep_hArg_116_Gen : nativeHeatExpArgGen 116 = nativeHeatExpArg nativeGap117Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_116_Gen]

theorem nativeHeatStep_hExp_116_Gen : nativeHeatExpGen 116 = nativeHeat116Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_116_Gen, nativeHeat116Exp_formula]

theorem nativeHeatStep_hCoef_116_Gen : nativeHeatCoefGen 116 = nativeHeat116Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_116_Gen, nativeHeat116Coef_formula]

theorem nativeHeatStep_hInit_116_Gen : nativeHeatInitGen 116 = nativeHeat116Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_116_Gen, nativeHeatStep_hVar_116_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat116Init00_formula
    · exact nativeHeat116Init01_formula
    · exact nativeHeat116Init02_formula
    · exact nativeHeat116Init03_formula
    · exact nativeHeat116Init04_formula
    · exact nativeHeat116Init05_formula
    · exact nativeHeat116Init06_formula
    · exact nativeHeat116Init07_formula
    · exact nativeHeat116Init08_formula
    · exact nativeHeat116Init09_formula
    · exact nativeHeat116Init10_formula
    · exact nativeHeat116Init11_formula
    · exact nativeHeat116Init12_formula
    · exact nativeHeat116Init13_formula
    · exact nativeHeat116Init14_formula
    · exact nativeHeat116Init15_formula
    · exact nativeHeat116Init16_formula
    · exact nativeHeat116Init17_formula
    · exact nativeHeat116Init18_formula
    · exact nativeHeat116Init19_formula
    · exact nativeHeat116Init20_formula
theorem nativeHeatStep_hBase_116_Gen : nativeHeatBaseGen 116 = nativeHeat116Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_116_Gen, nativeHeatStep_hInit_116_Gen, nativeHeat116Base_formula]

theorem nativeHeatStep_hFixed_116_Gen : nativeHeatFixedGen 116 = nativeHeat116Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_116_Gen, nativeHeatStep_hFr_116_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat116Fixed01_formula
    · exact nativeHeat116Fixed02_formula
    · exact nativeHeat116Fixed03_formula
    · exact nativeHeat116Fixed04_formula
    · exact nativeHeat116Fixed05_formula
    · exact nativeHeat116Fixed06_formula
    · exact nativeHeat116Fixed07_formula
    · exact nativeHeat116Fixed08_formula
    · exact nativeHeat116Fixed09_formula
    · exact nativeHeat116Fixed10_formula
    · exact nativeHeat116Fixed11_formula
    · exact nativeHeat116Fixed12_formula
    · exact nativeHeat116Fixed13_formula
    · exact nativeHeat116Fixed14_formula
    · exact nativeHeat116Fixed15_formula
    · exact nativeHeat116Fixed16_formula
    · exact nativeHeat116Fixed17_formula
    · exact nativeHeat116Fixed18_formula
    · exact nativeHeat116Fixed19_formula
    · exact nativeHeat116Fixed20_formula

theorem nativeHeatStep_chk_116_Gen :
    nativeHeatPassRootsOk nativeGap117Old nativeHeat116Frames nativeHeat116Coef nativeHeat116Fixed nativeHeat116Base 48 nativeHeat116Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_116_Gen : NativeHeatStepPassNum 116 := by
  refine nativeHeatStepPassNum_of_literals 116 nativeGap117Old nativeHeat116Frames (nativeHeatExpArg nativeGap117Old)
    nativeHeat116Exp nativeHeat116Coef nativeHeat116Fixed nativeHeat116Init nativeHeat116Base nativeHeatStep_hOld_116_Gen
    nativeHeatStep_hFr_116_Gen nativeHeatStep_hArg_116_Gen nativeHeatStep_hExp_116_Gen
    nativeHeatStep_hCoef_116_Gen nativeHeatStep_hFixed_116_Gen
    nativeHeatStep_hInit_116_Gen nativeHeatStep_hBase_116_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_116_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_116_Gen :
    nativeHeatY0Gen 116 = nativeShiftedFrame 1 (min nativeGap117Old.x nativeGap117Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_116_Gen, nativeHeatStep_hInd_116_Gen]

theorem nativeHeatStepFrameNum_116_Gen : NativeHeatStepFrameNum 116 := by
  have h1 := nativeHeatStep_hOld_116_Gen
  have h2 := nativeHeatStep_hInd_116_Gen
  have h3 := nativeHeatStep_hVar_116_Gen
  have h4 := nativeHeatStep_hQm_116_Gen
  have h5 := nativeHeatStep_hQN_116_Gen
  have h6 := nativeHeatStep_hY0_116_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_116_Gen : NativeHeatStepIndivNum 116 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 116 (by norm_num)) = nativeGap117Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_116_Gen]; exact nativeGap117Old_source
  · rw [hc, nativeHeatStep_hInd_116_Gen]; exact nativeGap117Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_116_Gen : nativeHeatY48Gen 116 = nativeHeat116Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_116_Gen, nativeHeatStep_hFr_116_Gen,
    nativeHeatStep_hCoef_116_Gen, nativeHeatStep_hFixed_116_Gen,
    nativeHeatStep_hBase_116_Gen]
  exact nativeHeat116All48

theorem nativeHeatResultGen_116 : nativeHeatResultGen 116 = nativeHeat116Result := by
  rw [← nativeHeat116Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_116_Gen, nativeHeatStep_hY0_116_Gen, nativeHeatStep_hExp_116_Gen,
    nativeHeatStep_hInit_116_Gen, nativeHeatStep_hFixed_116_Gen]

end ASDExplicitGamma.Native

end
