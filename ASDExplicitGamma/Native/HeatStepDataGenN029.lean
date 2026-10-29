module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat029Complete
public import ASDExplicitGamma.Numerics.Native.Gap030Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_029_Gen : nativeHeatOldRowGen 29 = nativeGap030Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_029_Gen : nativeHeatIndividualGen 29 = nativeGap030Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_029_Gen : nativeHeatGenVariance 29 = nativeHeat029Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_029_Gen, nativeHeat029Variance_formula]

theorem nativeHeatStep_hSpec_029_Gen : nativeHeatGenSpectral 29 = nativeHeat029Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_029_Gen, nativeHeat029Variance_formula]

theorem nativeHeatStep_hQm_029_Gen : nativeHeatGenQm 29 = nativeHeat029Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_029_Gen, nativeHeatStep_hSpec_029_Gen,
    nativeHeat029Qm_formula]

theorem nativeHeatStep_hQN_029_Gen : nativeHeatQNGen 29 = nativeHeat029QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_029_Gen, nativeHeat029QN_formula]

theorem nativeHeatStep_hFr_029_Gen : nativeHeatFramesGen 29 = nativeHeat029Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_029_Gen, nativeHeatStep_hInd_029_Gen,
    nativeHeatStep_hVar_029_Gen, nativeHeatStep_hQN_029_Gen, nativeHeat029Frames_formula]

theorem nativeHeatStep_hArg_029_Gen : nativeHeatExpArgGen 29 = nativeHeatExpArg nativeGap030Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_029_Gen]

theorem nativeHeatStep_hExp_029_Gen : nativeHeatExpGen 29 = nativeHeat029Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_029_Gen, nativeHeat029Exp_formula]

theorem nativeHeatStep_hCoef_029_Gen : nativeHeatCoefGen 29 = nativeHeat029Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_029_Gen, nativeHeat029Coef_formula]

theorem nativeHeatStep_hInit_029_Gen : nativeHeatInitGen 29 = nativeHeat029Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_029_Gen, nativeHeatStep_hVar_029_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat029Init00_formula
    · exact nativeHeat029Init01_formula
    · exact nativeHeat029Init02_formula
    · exact nativeHeat029Init03_formula
    · exact nativeHeat029Init04_formula
    · exact nativeHeat029Init05_formula
    · exact nativeHeat029Init06_formula
    · exact nativeHeat029Init07_formula
    · exact nativeHeat029Init08_formula
    · exact nativeHeat029Init09_formula
    · exact nativeHeat029Init10_formula
    · exact nativeHeat029Init11_formula
    · exact nativeHeat029Init12_formula
    · exact nativeHeat029Init13_formula
    · exact nativeHeat029Init14_formula
    · exact nativeHeat029Init15_formula
    · exact nativeHeat029Init16_formula
    · exact nativeHeat029Init17_formula
    · exact nativeHeat029Init18_formula
    · exact nativeHeat029Init19_formula
    · exact nativeHeat029Init20_formula
theorem nativeHeatStep_hBase_029_Gen : nativeHeatBaseGen 29 = nativeHeat029Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_029_Gen, nativeHeatStep_hInit_029_Gen, nativeHeat029Base_formula]

theorem nativeHeatStep_hFixed_029_Gen : nativeHeatFixedGen 29 = nativeHeat029Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_029_Gen, nativeHeatStep_hFr_029_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat029Fixed01_formula
    · exact nativeHeat029Fixed02_formula
    · exact nativeHeat029Fixed03_formula
    · exact nativeHeat029Fixed04_formula
    · exact nativeHeat029Fixed05_formula
    · exact nativeHeat029Fixed06_formula
    · exact nativeHeat029Fixed07_formula
    · exact nativeHeat029Fixed08_formula
    · exact nativeHeat029Fixed09_formula
    · exact nativeHeat029Fixed10_formula
    · exact nativeHeat029Fixed11_formula
    · exact nativeHeat029Fixed12_formula
    · exact nativeHeat029Fixed13_formula
    · exact nativeHeat029Fixed14_formula
    · exact nativeHeat029Fixed15_formula
    · exact nativeHeat029Fixed16_formula
    · exact nativeHeat029Fixed17_formula
    · exact nativeHeat029Fixed18_formula
    · exact nativeHeat029Fixed19_formula
    · exact nativeHeat029Fixed20_formula

theorem nativeHeatStep_chk_029_Gen :
    nativeHeatPassRootsOk nativeGap030Old nativeHeat029Frames nativeHeat029Coef nativeHeat029Fixed nativeHeat029Base 48 nativeHeat029Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_029_Gen : NativeHeatStepPassNum 29 := by
  refine nativeHeatStepPassNum_of_literals 29 nativeGap030Old nativeHeat029Frames (nativeHeatExpArg nativeGap030Old)
    nativeHeat029Exp nativeHeat029Coef nativeHeat029Fixed nativeHeat029Init nativeHeat029Base nativeHeatStep_hOld_029_Gen
    nativeHeatStep_hFr_029_Gen nativeHeatStep_hArg_029_Gen nativeHeatStep_hExp_029_Gen
    nativeHeatStep_hCoef_029_Gen nativeHeatStep_hFixed_029_Gen
    nativeHeatStep_hInit_029_Gen nativeHeatStep_hBase_029_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_029_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_029_Gen :
    nativeHeatY0Gen 29 = nativeShiftedFrame 1 (min nativeGap030Old.x nativeGap030Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_029_Gen, nativeHeatStep_hInd_029_Gen]

theorem nativeHeatStepFrameNum_029_Gen : NativeHeatStepFrameNum 29 := by
  have h1 := nativeHeatStep_hOld_029_Gen
  have h2 := nativeHeatStep_hInd_029_Gen
  have h3 := nativeHeatStep_hVar_029_Gen
  have h4 := nativeHeatStep_hQm_029_Gen
  have h5 := nativeHeatStep_hQN_029_Gen
  have h6 := nativeHeatStep_hY0_029_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_029_Gen : NativeHeatStepIndivNum 29 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 29 (by norm_num)) = nativeGap030Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_029_Gen]; exact nativeGap030Old_source
  · rw [hc, nativeHeatStep_hInd_029_Gen]; exact nativeGap030Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_029_Gen : nativeHeatY48Gen 29 = nativeHeat029Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_029_Gen, nativeHeatStep_hFr_029_Gen,
    nativeHeatStep_hCoef_029_Gen, nativeHeatStep_hFixed_029_Gen,
    nativeHeatStep_hBase_029_Gen]
  exact nativeHeat029All48

theorem nativeHeatResultGen_029 : nativeHeatResultGen 29 = nativeHeat029Result := by
  rw [← nativeHeat029Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_029_Gen, nativeHeatStep_hY0_029_Gen, nativeHeatStep_hExp_029_Gen,
    nativeHeatStep_hInit_029_Gen, nativeHeatStep_hFixed_029_Gen]

end ASDExplicitGamma.Native

end
