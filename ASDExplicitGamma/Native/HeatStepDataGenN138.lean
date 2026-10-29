module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat138Complete
public import ASDExplicitGamma.Numerics.Native.Gap139Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_138_Gen : nativeHeatOldRowGen 138 = nativeGap139Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_138_Gen : nativeHeatIndividualGen 138 = nativeGap139Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_138_Gen : nativeHeatGenVariance 138 = nativeHeat138Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_138_Gen, nativeHeat138Variance_formula]

theorem nativeHeatStep_hSpec_138_Gen : nativeHeatGenSpectral 138 = nativeHeat138Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_138_Gen, nativeHeat138Variance_formula]

theorem nativeHeatStep_hQm_138_Gen : nativeHeatGenQm 138 = nativeHeat138Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_138_Gen, nativeHeatStep_hSpec_138_Gen,
    nativeHeat138Qm_formula]

theorem nativeHeatStep_hQN_138_Gen : nativeHeatQNGen 138 = nativeHeat138QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_138_Gen, nativeHeat138QN_formula]

theorem nativeHeatStep_hFr_138_Gen : nativeHeatFramesGen 138 = nativeHeat138Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_138_Gen, nativeHeatStep_hInd_138_Gen,
    nativeHeatStep_hVar_138_Gen, nativeHeatStep_hQN_138_Gen, nativeHeat138Frames_formula]

theorem nativeHeatStep_hArg_138_Gen : nativeHeatExpArgGen 138 = nativeHeatExpArg nativeGap139Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_138_Gen]

theorem nativeHeatStep_hExp_138_Gen : nativeHeatExpGen 138 = nativeHeat138Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_138_Gen, nativeHeat138Exp_formula]

theorem nativeHeatStep_hCoef_138_Gen : nativeHeatCoefGen 138 = nativeHeat138Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_138_Gen, nativeHeat138Coef_formula]

theorem nativeHeatStep_hInit_138_Gen : nativeHeatInitGen 138 = nativeHeat138Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_138_Gen, nativeHeatStep_hVar_138_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat138Init00_formula
    · exact nativeHeat138Init01_formula
    · exact nativeHeat138Init02_formula
    · exact nativeHeat138Init03_formula
    · exact nativeHeat138Init04_formula
    · exact nativeHeat138Init05_formula
    · exact nativeHeat138Init06_formula
    · exact nativeHeat138Init07_formula
    · exact nativeHeat138Init08_formula
    · exact nativeHeat138Init09_formula
    · exact nativeHeat138Init10_formula
    · exact nativeHeat138Init11_formula
    · exact nativeHeat138Init12_formula
    · exact nativeHeat138Init13_formula
    · exact nativeHeat138Init14_formula
    · exact nativeHeat138Init15_formula
    · exact nativeHeat138Init16_formula
    · exact nativeHeat138Init17_formula
    · exact nativeHeat138Init18_formula
    · exact nativeHeat138Init19_formula
    · exact nativeHeat138Init20_formula
theorem nativeHeatStep_hBase_138_Gen : nativeHeatBaseGen 138 = nativeHeat138Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_138_Gen, nativeHeatStep_hInit_138_Gen, nativeHeat138Base_formula]

theorem nativeHeatStep_hFixed_138_Gen : nativeHeatFixedGen 138 = nativeHeat138Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_138_Gen, nativeHeatStep_hFr_138_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat138Fixed01_formula
    · exact nativeHeat138Fixed02_formula
    · exact nativeHeat138Fixed03_formula
    · exact nativeHeat138Fixed04_formula
    · exact nativeHeat138Fixed05_formula
    · exact nativeHeat138Fixed06_formula
    · exact nativeHeat138Fixed07_formula
    · exact nativeHeat138Fixed08_formula
    · exact nativeHeat138Fixed09_formula
    · exact nativeHeat138Fixed10_formula
    · exact nativeHeat138Fixed11_formula
    · exact nativeHeat138Fixed12_formula
    · exact nativeHeat138Fixed13_formula
    · exact nativeHeat138Fixed14_formula
    · exact nativeHeat138Fixed15_formula
    · exact nativeHeat138Fixed16_formula
    · exact nativeHeat138Fixed17_formula
    · exact nativeHeat138Fixed18_formula
    · exact nativeHeat138Fixed19_formula
    · exact nativeHeat138Fixed20_formula

theorem nativeHeatStep_chk_138_Gen :
    nativeHeatPassRootsOk nativeGap139Old nativeHeat138Frames nativeHeat138Coef nativeHeat138Fixed nativeHeat138Base 48 nativeHeat138Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_138_Gen : NativeHeatStepPassNum 138 := by
  refine nativeHeatStepPassNum_of_literals 138 nativeGap139Old nativeHeat138Frames (nativeHeatExpArg nativeGap139Old)
    nativeHeat138Exp nativeHeat138Coef nativeHeat138Fixed nativeHeat138Init nativeHeat138Base nativeHeatStep_hOld_138_Gen
    nativeHeatStep_hFr_138_Gen nativeHeatStep_hArg_138_Gen nativeHeatStep_hExp_138_Gen
    nativeHeatStep_hCoef_138_Gen nativeHeatStep_hFixed_138_Gen
    nativeHeatStep_hInit_138_Gen nativeHeatStep_hBase_138_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_138_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_138_Gen :
    nativeHeatY0Gen 138 = nativeShiftedFrame 1 (min nativeGap139Old.x nativeGap139Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_138_Gen, nativeHeatStep_hInd_138_Gen]

theorem nativeHeatStepFrameNum_138_Gen : NativeHeatStepFrameNum 138 := by
  have h1 := nativeHeatStep_hOld_138_Gen
  have h2 := nativeHeatStep_hInd_138_Gen
  have h3 := nativeHeatStep_hVar_138_Gen
  have h4 := nativeHeatStep_hQm_138_Gen
  have h5 := nativeHeatStep_hQN_138_Gen
  have h6 := nativeHeatStep_hY0_138_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_138_Gen : NativeHeatStepIndivNum 138 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 138 (by norm_num)) = nativeGap139Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_138_Gen]; exact nativeGap139Old_source
  · rw [hc, nativeHeatStep_hInd_138_Gen]; exact nativeGap139Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_138_Gen : nativeHeatY48Gen 138 = nativeHeat138Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_138_Gen, nativeHeatStep_hFr_138_Gen,
    nativeHeatStep_hCoef_138_Gen, nativeHeatStep_hFixed_138_Gen,
    nativeHeatStep_hBase_138_Gen]
  exact nativeHeat138All48

theorem nativeHeatResultGen_138 : nativeHeatResultGen 138 = nativeHeat138Result := by
  rw [← nativeHeat138Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_138_Gen, nativeHeatStep_hY0_138_Gen, nativeHeatStep_hExp_138_Gen,
    nativeHeatStep_hInit_138_Gen, nativeHeatStep_hFixed_138_Gen]

end ASDExplicitGamma.Native

end
