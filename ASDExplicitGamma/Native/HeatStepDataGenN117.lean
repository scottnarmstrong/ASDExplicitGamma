module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat117Complete
public import ASDExplicitGamma.Numerics.Native.Gap118Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_117_Gen : nativeHeatOldRowGen 117 = nativeGap118Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_117_Gen : nativeHeatIndividualGen 117 = nativeGap118Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_117_Gen : nativeHeatGenVariance 117 = nativeHeat117Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_117_Gen, nativeHeat117Variance_formula]

theorem nativeHeatStep_hSpec_117_Gen : nativeHeatGenSpectral 117 = nativeHeat117Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_117_Gen, nativeHeat117Variance_formula]

theorem nativeHeatStep_hQm_117_Gen : nativeHeatGenQm 117 = nativeHeat117Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_117_Gen, nativeHeatStep_hSpec_117_Gen,
    nativeHeat117Qm_formula]

theorem nativeHeatStep_hQN_117_Gen : nativeHeatQNGen 117 = nativeHeat117QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_117_Gen, nativeHeat117QN_formula]

theorem nativeHeatStep_hFr_117_Gen : nativeHeatFramesGen 117 = nativeHeat117Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_117_Gen, nativeHeatStep_hInd_117_Gen,
    nativeHeatStep_hVar_117_Gen, nativeHeatStep_hQN_117_Gen, nativeHeat117Frames_formula]

theorem nativeHeatStep_hArg_117_Gen : nativeHeatExpArgGen 117 = nativeHeatExpArg nativeGap118Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_117_Gen]

theorem nativeHeatStep_hExp_117_Gen : nativeHeatExpGen 117 = nativeHeat117Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_117_Gen, nativeHeat117Exp_formula]

theorem nativeHeatStep_hCoef_117_Gen : nativeHeatCoefGen 117 = nativeHeat117Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_117_Gen, nativeHeat117Coef_formula]

theorem nativeHeatStep_hInit_117_Gen : nativeHeatInitGen 117 = nativeHeat117Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_117_Gen, nativeHeatStep_hVar_117_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat117Init00_formula
    · exact nativeHeat117Init01_formula
    · exact nativeHeat117Init02_formula
    · exact nativeHeat117Init03_formula
    · exact nativeHeat117Init04_formula
    · exact nativeHeat117Init05_formula
    · exact nativeHeat117Init06_formula
    · exact nativeHeat117Init07_formula
    · exact nativeHeat117Init08_formula
    · exact nativeHeat117Init09_formula
    · exact nativeHeat117Init10_formula
    · exact nativeHeat117Init11_formula
    · exact nativeHeat117Init12_formula
    · exact nativeHeat117Init13_formula
    · exact nativeHeat117Init14_formula
    · exact nativeHeat117Init15_formula
    · exact nativeHeat117Init16_formula
    · exact nativeHeat117Init17_formula
    · exact nativeHeat117Init18_formula
    · exact nativeHeat117Init19_formula
    · exact nativeHeat117Init20_formula
theorem nativeHeatStep_hBase_117_Gen : nativeHeatBaseGen 117 = nativeHeat117Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_117_Gen, nativeHeatStep_hInit_117_Gen, nativeHeat117Base_formula]

theorem nativeHeatStep_hFixed_117_Gen : nativeHeatFixedGen 117 = nativeHeat117Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_117_Gen, nativeHeatStep_hFr_117_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat117Fixed01_formula
    · exact nativeHeat117Fixed02_formula
    · exact nativeHeat117Fixed03_formula
    · exact nativeHeat117Fixed04_formula
    · exact nativeHeat117Fixed05_formula
    · exact nativeHeat117Fixed06_formula
    · exact nativeHeat117Fixed07_formula
    · exact nativeHeat117Fixed08_formula
    · exact nativeHeat117Fixed09_formula
    · exact nativeHeat117Fixed10_formula
    · exact nativeHeat117Fixed11_formula
    · exact nativeHeat117Fixed12_formula
    · exact nativeHeat117Fixed13_formula
    · exact nativeHeat117Fixed14_formula
    · exact nativeHeat117Fixed15_formula
    · exact nativeHeat117Fixed16_formula
    · exact nativeHeat117Fixed17_formula
    · exact nativeHeat117Fixed18_formula
    · exact nativeHeat117Fixed19_formula
    · exact nativeHeat117Fixed20_formula

theorem nativeHeatStep_chk_117_Gen :
    nativeHeatPassRootsOk nativeGap118Old nativeHeat117Frames nativeHeat117Coef nativeHeat117Fixed nativeHeat117Base 48 nativeHeat117Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_117_Gen : NativeHeatStepPassNum 117 := by
  refine nativeHeatStepPassNum_of_literals 117 nativeGap118Old nativeHeat117Frames (nativeHeatExpArg nativeGap118Old)
    nativeHeat117Exp nativeHeat117Coef nativeHeat117Fixed nativeHeat117Init nativeHeat117Base nativeHeatStep_hOld_117_Gen
    nativeHeatStep_hFr_117_Gen nativeHeatStep_hArg_117_Gen nativeHeatStep_hExp_117_Gen
    nativeHeatStep_hCoef_117_Gen nativeHeatStep_hFixed_117_Gen
    nativeHeatStep_hInit_117_Gen nativeHeatStep_hBase_117_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_117_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_117_Gen :
    nativeHeatY0Gen 117 = nativeShiftedFrame 1 (min nativeGap118Old.x nativeGap118Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_117_Gen, nativeHeatStep_hInd_117_Gen]

theorem nativeHeatStepFrameNum_117_Gen : NativeHeatStepFrameNum 117 := by
  have h1 := nativeHeatStep_hOld_117_Gen
  have h2 := nativeHeatStep_hInd_117_Gen
  have h3 := nativeHeatStep_hVar_117_Gen
  have h4 := nativeHeatStep_hQm_117_Gen
  have h5 := nativeHeatStep_hQN_117_Gen
  have h6 := nativeHeatStep_hY0_117_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_117_Gen : NativeHeatStepIndivNum 117 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 117 (by norm_num)) = nativeGap118Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_117_Gen]; exact nativeGap118Old_source
  · rw [hc, nativeHeatStep_hInd_117_Gen]; exact nativeGap118Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_117_Gen : nativeHeatY48Gen 117 = nativeHeat117Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_117_Gen, nativeHeatStep_hFr_117_Gen,
    nativeHeatStep_hCoef_117_Gen, nativeHeatStep_hFixed_117_Gen,
    nativeHeatStep_hBase_117_Gen]
  exact nativeHeat117All48

theorem nativeHeatResultGen_117 : nativeHeatResultGen 117 = nativeHeat117Result := by
  rw [← nativeHeat117Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_117_Gen, nativeHeatStep_hY0_117_Gen, nativeHeatStep_hExp_117_Gen,
    nativeHeatStep_hInit_117_Gen, nativeHeatStep_hFixed_117_Gen]

end ASDExplicitGamma.Native

end
