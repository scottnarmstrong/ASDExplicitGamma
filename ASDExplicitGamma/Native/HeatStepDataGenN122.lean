module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat122Complete
public import ASDExplicitGamma.Numerics.Native.Gap123Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_122_Gen : nativeHeatOldRowGen 122 = nativeGap123Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_122_Gen : nativeHeatIndividualGen 122 = nativeGap123Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_122_Gen : nativeHeatGenVariance 122 = nativeHeat122Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_122_Gen, nativeHeat122Variance_formula]

theorem nativeHeatStep_hSpec_122_Gen : nativeHeatGenSpectral 122 = nativeHeat122Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_122_Gen, nativeHeat122Variance_formula]

theorem nativeHeatStep_hQm_122_Gen : nativeHeatGenQm 122 = nativeHeat122Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_122_Gen, nativeHeatStep_hSpec_122_Gen,
    nativeHeat122Qm_formula]

theorem nativeHeatStep_hQN_122_Gen : nativeHeatQNGen 122 = nativeHeat122QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_122_Gen, nativeHeat122QN_formula]

theorem nativeHeatStep_hFr_122_Gen : nativeHeatFramesGen 122 = nativeHeat122Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_122_Gen, nativeHeatStep_hInd_122_Gen,
    nativeHeatStep_hVar_122_Gen, nativeHeatStep_hQN_122_Gen, nativeHeat122Frames_formula]

theorem nativeHeatStep_hArg_122_Gen : nativeHeatExpArgGen 122 = nativeHeatExpArg nativeGap123Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_122_Gen]

theorem nativeHeatStep_hExp_122_Gen : nativeHeatExpGen 122 = nativeHeat122Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_122_Gen, nativeHeat122Exp_formula]

theorem nativeHeatStep_hCoef_122_Gen : nativeHeatCoefGen 122 = nativeHeat122Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_122_Gen, nativeHeat122Coef_formula]

theorem nativeHeatStep_hInit_122_Gen : nativeHeatInitGen 122 = nativeHeat122Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_122_Gen, nativeHeatStep_hVar_122_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat122Init00_formula
    · exact nativeHeat122Init01_formula
    · exact nativeHeat122Init02_formula
    · exact nativeHeat122Init03_formula
    · exact nativeHeat122Init04_formula
    · exact nativeHeat122Init05_formula
    · exact nativeHeat122Init06_formula
    · exact nativeHeat122Init07_formula
    · exact nativeHeat122Init08_formula
    · exact nativeHeat122Init09_formula
    · exact nativeHeat122Init10_formula
    · exact nativeHeat122Init11_formula
    · exact nativeHeat122Init12_formula
    · exact nativeHeat122Init13_formula
    · exact nativeHeat122Init14_formula
    · exact nativeHeat122Init15_formula
    · exact nativeHeat122Init16_formula
    · exact nativeHeat122Init17_formula
    · exact nativeHeat122Init18_formula
    · exact nativeHeat122Init19_formula
    · exact nativeHeat122Init20_formula
theorem nativeHeatStep_hBase_122_Gen : nativeHeatBaseGen 122 = nativeHeat122Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_122_Gen, nativeHeatStep_hInit_122_Gen, nativeHeat122Base_formula]

theorem nativeHeatStep_hFixed_122_Gen : nativeHeatFixedGen 122 = nativeHeat122Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_122_Gen, nativeHeatStep_hFr_122_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat122Fixed01_formula
    · exact nativeHeat122Fixed02_formula
    · exact nativeHeat122Fixed03_formula
    · exact nativeHeat122Fixed04_formula
    · exact nativeHeat122Fixed05_formula
    · exact nativeHeat122Fixed06_formula
    · exact nativeHeat122Fixed07_formula
    · exact nativeHeat122Fixed08_formula
    · exact nativeHeat122Fixed09_formula
    · exact nativeHeat122Fixed10_formula
    · exact nativeHeat122Fixed11_formula
    · exact nativeHeat122Fixed12_formula
    · exact nativeHeat122Fixed13_formula
    · exact nativeHeat122Fixed14_formula
    · exact nativeHeat122Fixed15_formula
    · exact nativeHeat122Fixed16_formula
    · exact nativeHeat122Fixed17_formula
    · exact nativeHeat122Fixed18_formula
    · exact nativeHeat122Fixed19_formula
    · exact nativeHeat122Fixed20_formula

theorem nativeHeatStep_chk_122_Gen :
    nativeHeatPassRootsOk nativeGap123Old nativeHeat122Frames nativeHeat122Coef nativeHeat122Fixed nativeHeat122Base 48 nativeHeat122Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_122_Gen : NativeHeatStepPassNum 122 := by
  refine nativeHeatStepPassNum_of_literals 122 nativeGap123Old nativeHeat122Frames (nativeHeatExpArg nativeGap123Old)
    nativeHeat122Exp nativeHeat122Coef nativeHeat122Fixed nativeHeat122Init nativeHeat122Base nativeHeatStep_hOld_122_Gen
    nativeHeatStep_hFr_122_Gen nativeHeatStep_hArg_122_Gen nativeHeatStep_hExp_122_Gen
    nativeHeatStep_hCoef_122_Gen nativeHeatStep_hFixed_122_Gen
    nativeHeatStep_hInit_122_Gen nativeHeatStep_hBase_122_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_122_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_122_Gen :
    nativeHeatY0Gen 122 = nativeShiftedFrame 1 (min nativeGap123Old.x nativeGap123Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_122_Gen, nativeHeatStep_hInd_122_Gen]

theorem nativeHeatStepFrameNum_122_Gen : NativeHeatStepFrameNum 122 := by
  have h1 := nativeHeatStep_hOld_122_Gen
  have h2 := nativeHeatStep_hInd_122_Gen
  have h3 := nativeHeatStep_hVar_122_Gen
  have h4 := nativeHeatStep_hQm_122_Gen
  have h5 := nativeHeatStep_hQN_122_Gen
  have h6 := nativeHeatStep_hY0_122_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_122_Gen : NativeHeatStepIndivNum 122 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 122 (by norm_num)) = nativeGap123Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_122_Gen]; exact nativeGap123Old_source
  · rw [hc, nativeHeatStep_hInd_122_Gen]; exact nativeGap123Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_122_Gen : nativeHeatY48Gen 122 = nativeHeat122Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_122_Gen, nativeHeatStep_hFr_122_Gen,
    nativeHeatStep_hCoef_122_Gen, nativeHeatStep_hFixed_122_Gen,
    nativeHeatStep_hBase_122_Gen]
  exact nativeHeat122All48

theorem nativeHeatResultGen_122 : nativeHeatResultGen 122 = nativeHeat122Result := by
  rw [← nativeHeat122Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_122_Gen, nativeHeatStep_hY0_122_Gen, nativeHeatStep_hExp_122_Gen,
    nativeHeatStep_hInit_122_Gen, nativeHeatStep_hFixed_122_Gen]

end ASDExplicitGamma.Native

end
