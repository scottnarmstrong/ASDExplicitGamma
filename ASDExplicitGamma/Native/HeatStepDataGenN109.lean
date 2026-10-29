module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat109Complete
public import ASDExplicitGamma.Numerics.Native.Gap110Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_109_Gen : nativeHeatOldRowGen 109 = nativeGap110Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_109_Gen : nativeHeatIndividualGen 109 = nativeGap110Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_109_Gen : nativeHeatGenVariance 109 = nativeHeat109Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_109_Gen, nativeHeat109Variance_formula]

theorem nativeHeatStep_hSpec_109_Gen : nativeHeatGenSpectral 109 = nativeHeat109Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_109_Gen, nativeHeat109Variance_formula]

theorem nativeHeatStep_hQm_109_Gen : nativeHeatGenQm 109 = nativeHeat109Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_109_Gen, nativeHeatStep_hSpec_109_Gen,
    nativeHeat109Qm_formula]

theorem nativeHeatStep_hQN_109_Gen : nativeHeatQNGen 109 = nativeHeat109QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_109_Gen, nativeHeat109QN_formula]

theorem nativeHeatStep_hFr_109_Gen : nativeHeatFramesGen 109 = nativeHeat109Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_109_Gen, nativeHeatStep_hInd_109_Gen,
    nativeHeatStep_hVar_109_Gen, nativeHeatStep_hQN_109_Gen, nativeHeat109Frames_formula]

theorem nativeHeatStep_hArg_109_Gen : nativeHeatExpArgGen 109 = nativeHeatExpArg nativeGap110Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_109_Gen]

theorem nativeHeatStep_hExp_109_Gen : nativeHeatExpGen 109 = nativeHeat109Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_109_Gen, nativeHeat109Exp_formula]

theorem nativeHeatStep_hCoef_109_Gen : nativeHeatCoefGen 109 = nativeHeat109Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_109_Gen, nativeHeat109Coef_formula]

theorem nativeHeatStep_hInit_109_Gen : nativeHeatInitGen 109 = nativeHeat109Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_109_Gen, nativeHeatStep_hVar_109_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat109Init00_formula
    · exact nativeHeat109Init01_formula
    · exact nativeHeat109Init02_formula
    · exact nativeHeat109Init03_formula
    · exact nativeHeat109Init04_formula
    · exact nativeHeat109Init05_formula
    · exact nativeHeat109Init06_formula
    · exact nativeHeat109Init07_formula
    · exact nativeHeat109Init08_formula
    · exact nativeHeat109Init09_formula
    · exact nativeHeat109Init10_formula
    · exact nativeHeat109Init11_formula
    · exact nativeHeat109Init12_formula
    · exact nativeHeat109Init13_formula
    · exact nativeHeat109Init14_formula
    · exact nativeHeat109Init15_formula
    · exact nativeHeat109Init16_formula
    · exact nativeHeat109Init17_formula
    · exact nativeHeat109Init18_formula
    · exact nativeHeat109Init19_formula
    · exact nativeHeat109Init20_formula
theorem nativeHeatStep_hBase_109_Gen : nativeHeatBaseGen 109 = nativeHeat109Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_109_Gen, nativeHeatStep_hInit_109_Gen, nativeHeat109Base_formula]

theorem nativeHeatStep_hFixed_109_Gen : nativeHeatFixedGen 109 = nativeHeat109Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_109_Gen, nativeHeatStep_hFr_109_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat109Fixed01_formula
    · exact nativeHeat109Fixed02_formula
    · exact nativeHeat109Fixed03_formula
    · exact nativeHeat109Fixed04_formula
    · exact nativeHeat109Fixed05_formula
    · exact nativeHeat109Fixed06_formula
    · exact nativeHeat109Fixed07_formula
    · exact nativeHeat109Fixed08_formula
    · exact nativeHeat109Fixed09_formula
    · exact nativeHeat109Fixed10_formula
    · exact nativeHeat109Fixed11_formula
    · exact nativeHeat109Fixed12_formula
    · exact nativeHeat109Fixed13_formula
    · exact nativeHeat109Fixed14_formula
    · exact nativeHeat109Fixed15_formula
    · exact nativeHeat109Fixed16_formula
    · exact nativeHeat109Fixed17_formula
    · exact nativeHeat109Fixed18_formula
    · exact nativeHeat109Fixed19_formula
    · exact nativeHeat109Fixed20_formula

theorem nativeHeatStep_chk_109_Gen :
    nativeHeatPassRootsOk nativeGap110Old nativeHeat109Frames nativeHeat109Coef nativeHeat109Fixed nativeHeat109Base 48 nativeHeat109Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_109_Gen : NativeHeatStepPassNum 109 := by
  refine nativeHeatStepPassNum_of_literals 109 nativeGap110Old nativeHeat109Frames (nativeHeatExpArg nativeGap110Old)
    nativeHeat109Exp nativeHeat109Coef nativeHeat109Fixed nativeHeat109Init nativeHeat109Base nativeHeatStep_hOld_109_Gen
    nativeHeatStep_hFr_109_Gen nativeHeatStep_hArg_109_Gen nativeHeatStep_hExp_109_Gen
    nativeHeatStep_hCoef_109_Gen nativeHeatStep_hFixed_109_Gen
    nativeHeatStep_hInit_109_Gen nativeHeatStep_hBase_109_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_109_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_109_Gen :
    nativeHeatY0Gen 109 = nativeShiftedFrame 1 (min nativeGap110Old.x nativeGap110Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_109_Gen, nativeHeatStep_hInd_109_Gen]

theorem nativeHeatStepFrameNum_109_Gen : NativeHeatStepFrameNum 109 := by
  have h1 := nativeHeatStep_hOld_109_Gen
  have h2 := nativeHeatStep_hInd_109_Gen
  have h3 := nativeHeatStep_hVar_109_Gen
  have h4 := nativeHeatStep_hQm_109_Gen
  have h5 := nativeHeatStep_hQN_109_Gen
  have h6 := nativeHeatStep_hY0_109_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_109_Gen : NativeHeatStepIndivNum 109 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 109 (by norm_num)) = nativeGap110Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_109_Gen]; exact nativeGap110Old_source
  · rw [hc, nativeHeatStep_hInd_109_Gen]; exact nativeGap110Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_109_Gen : nativeHeatY48Gen 109 = nativeHeat109Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_109_Gen, nativeHeatStep_hFr_109_Gen,
    nativeHeatStep_hCoef_109_Gen, nativeHeatStep_hFixed_109_Gen,
    nativeHeatStep_hBase_109_Gen]
  exact nativeHeat109All48

theorem nativeHeatResultGen_109 : nativeHeatResultGen 109 = nativeHeat109Result := by
  rw [← nativeHeat109Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_109_Gen, nativeHeatStep_hY0_109_Gen, nativeHeatStep_hExp_109_Gen,
    nativeHeatStep_hInit_109_Gen, nativeHeatStep_hFixed_109_Gen]

end ASDExplicitGamma.Native

end
