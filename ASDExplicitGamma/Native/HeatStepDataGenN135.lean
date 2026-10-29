module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat135Complete
public import ASDExplicitGamma.Numerics.Native.Gap136Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_135_Gen : nativeHeatOldRowGen 135 = nativeGap136Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_135_Gen : nativeHeatIndividualGen 135 = nativeGap136Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_135_Gen : nativeHeatGenVariance 135 = nativeHeat135Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_135_Gen, nativeHeat135Variance_formula]

theorem nativeHeatStep_hSpec_135_Gen : nativeHeatGenSpectral 135 = nativeHeat135Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_135_Gen, nativeHeat135Variance_formula]

theorem nativeHeatStep_hQm_135_Gen : nativeHeatGenQm 135 = nativeHeat135Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_135_Gen, nativeHeatStep_hSpec_135_Gen,
    nativeHeat135Qm_formula]

theorem nativeHeatStep_hQN_135_Gen : nativeHeatQNGen 135 = nativeHeat135QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_135_Gen, nativeHeat135QN_formula]

theorem nativeHeatStep_hFr_135_Gen : nativeHeatFramesGen 135 = nativeHeat135Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_135_Gen, nativeHeatStep_hInd_135_Gen,
    nativeHeatStep_hVar_135_Gen, nativeHeatStep_hQN_135_Gen, nativeHeat135Frames_formula]

theorem nativeHeatStep_hArg_135_Gen : nativeHeatExpArgGen 135 = nativeHeatExpArg nativeGap136Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_135_Gen]

theorem nativeHeatStep_hExp_135_Gen : nativeHeatExpGen 135 = nativeHeat135Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_135_Gen, nativeHeat135Exp_formula]

theorem nativeHeatStep_hCoef_135_Gen : nativeHeatCoefGen 135 = nativeHeat135Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_135_Gen, nativeHeat135Coef_formula]

theorem nativeHeatStep_hInit_135_Gen : nativeHeatInitGen 135 = nativeHeat135Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_135_Gen, nativeHeatStep_hVar_135_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat135Init00_formula
    · exact nativeHeat135Init01_formula
    · exact nativeHeat135Init02_formula
    · exact nativeHeat135Init03_formula
    · exact nativeHeat135Init04_formula
    · exact nativeHeat135Init05_formula
    · exact nativeHeat135Init06_formula
    · exact nativeHeat135Init07_formula
    · exact nativeHeat135Init08_formula
    · exact nativeHeat135Init09_formula
    · exact nativeHeat135Init10_formula
    · exact nativeHeat135Init11_formula
    · exact nativeHeat135Init12_formula
    · exact nativeHeat135Init13_formula
    · exact nativeHeat135Init14_formula
    · exact nativeHeat135Init15_formula
    · exact nativeHeat135Init16_formula
    · exact nativeHeat135Init17_formula
    · exact nativeHeat135Init18_formula
    · exact nativeHeat135Init19_formula
    · exact nativeHeat135Init20_formula
theorem nativeHeatStep_hBase_135_Gen : nativeHeatBaseGen 135 = nativeHeat135Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_135_Gen, nativeHeatStep_hInit_135_Gen, nativeHeat135Base_formula]

theorem nativeHeatStep_hFixed_135_Gen : nativeHeatFixedGen 135 = nativeHeat135Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_135_Gen, nativeHeatStep_hFr_135_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat135Fixed01_formula
    · exact nativeHeat135Fixed02_formula
    · exact nativeHeat135Fixed03_formula
    · exact nativeHeat135Fixed04_formula
    · exact nativeHeat135Fixed05_formula
    · exact nativeHeat135Fixed06_formula
    · exact nativeHeat135Fixed07_formula
    · exact nativeHeat135Fixed08_formula
    · exact nativeHeat135Fixed09_formula
    · exact nativeHeat135Fixed10_formula
    · exact nativeHeat135Fixed11_formula
    · exact nativeHeat135Fixed12_formula
    · exact nativeHeat135Fixed13_formula
    · exact nativeHeat135Fixed14_formula
    · exact nativeHeat135Fixed15_formula
    · exact nativeHeat135Fixed16_formula
    · exact nativeHeat135Fixed17_formula
    · exact nativeHeat135Fixed18_formula
    · exact nativeHeat135Fixed19_formula
    · exact nativeHeat135Fixed20_formula

theorem nativeHeatStep_chk_135_Gen :
    nativeHeatPassRootsOk nativeGap136Old nativeHeat135Frames nativeHeat135Coef nativeHeat135Fixed nativeHeat135Base 48 nativeHeat135Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_135_Gen : NativeHeatStepPassNum 135 := by
  refine nativeHeatStepPassNum_of_literals 135 nativeGap136Old nativeHeat135Frames (nativeHeatExpArg nativeGap136Old)
    nativeHeat135Exp nativeHeat135Coef nativeHeat135Fixed nativeHeat135Init nativeHeat135Base nativeHeatStep_hOld_135_Gen
    nativeHeatStep_hFr_135_Gen nativeHeatStep_hArg_135_Gen nativeHeatStep_hExp_135_Gen
    nativeHeatStep_hCoef_135_Gen nativeHeatStep_hFixed_135_Gen
    nativeHeatStep_hInit_135_Gen nativeHeatStep_hBase_135_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_135_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_135_Gen :
    nativeHeatY0Gen 135 = nativeShiftedFrame 1 (min nativeGap136Old.x nativeGap136Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_135_Gen, nativeHeatStep_hInd_135_Gen]

theorem nativeHeatStepFrameNum_135_Gen : NativeHeatStepFrameNum 135 := by
  have h1 := nativeHeatStep_hOld_135_Gen
  have h2 := nativeHeatStep_hInd_135_Gen
  have h3 := nativeHeatStep_hVar_135_Gen
  have h4 := nativeHeatStep_hQm_135_Gen
  have h5 := nativeHeatStep_hQN_135_Gen
  have h6 := nativeHeatStep_hY0_135_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_135_Gen : NativeHeatStepIndivNum 135 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 135 (by norm_num)) = nativeGap136Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_135_Gen]; exact nativeGap136Old_source
  · rw [hc, nativeHeatStep_hInd_135_Gen]; exact nativeGap136Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_135_Gen : nativeHeatY48Gen 135 = nativeHeat135Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_135_Gen, nativeHeatStep_hFr_135_Gen,
    nativeHeatStep_hCoef_135_Gen, nativeHeatStep_hFixed_135_Gen,
    nativeHeatStep_hBase_135_Gen]
  exact nativeHeat135All48

theorem nativeHeatResultGen_135 : nativeHeatResultGen 135 = nativeHeat135Result := by
  rw [← nativeHeat135Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_135_Gen, nativeHeatStep_hY0_135_Gen, nativeHeatStep_hExp_135_Gen,
    nativeHeatStep_hInit_135_Gen, nativeHeatStep_hFixed_135_Gen]

end ASDExplicitGamma.Native

end
