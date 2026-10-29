module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat017Complete
public import ASDExplicitGamma.Numerics.Native.Gap018Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_017_Gen : nativeHeatOldRowGen 17 = nativeGap018Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_017_Gen : nativeHeatIndividualGen 17 = nativeGap018Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_017_Gen : nativeHeatGenVariance 17 = nativeHeat017Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_017_Gen, nativeHeat017Variance_formula]

theorem nativeHeatStep_hSpec_017_Gen : nativeHeatGenSpectral 17 = nativeHeat017Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_017_Gen, nativeHeat017Variance_formula]

theorem nativeHeatStep_hQm_017_Gen : nativeHeatGenQm 17 = nativeHeat017Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_017_Gen, nativeHeatStep_hSpec_017_Gen,
    nativeHeat017Qm_formula]

theorem nativeHeatStep_hQN_017_Gen : nativeHeatQNGen 17 = nativeHeat017QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_017_Gen, nativeHeat017QN_formula]

theorem nativeHeatStep_hFr_017_Gen : nativeHeatFramesGen 17 = nativeHeat017Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_017_Gen, nativeHeatStep_hInd_017_Gen,
    nativeHeatStep_hVar_017_Gen, nativeHeatStep_hQN_017_Gen, nativeHeat017Frames_formula]

theorem nativeHeatStep_hArg_017_Gen : nativeHeatExpArgGen 17 = nativeHeatExpArg nativeGap018Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_017_Gen]

theorem nativeHeatStep_hExp_017_Gen : nativeHeatExpGen 17 = nativeHeat017Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_017_Gen, nativeHeat017Exp_formula]

theorem nativeHeatStep_hCoef_017_Gen : nativeHeatCoefGen 17 = nativeHeat017Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_017_Gen, nativeHeat017Coef_formula]

theorem nativeHeatStep_hInit_017_Gen : nativeHeatInitGen 17 = nativeHeat017Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_017_Gen, nativeHeatStep_hVar_017_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat017Init00_formula
    · exact nativeHeat017Init01_formula
    · exact nativeHeat017Init02_formula
    · exact nativeHeat017Init03_formula
    · exact nativeHeat017Init04_formula
    · exact nativeHeat017Init05_formula
    · exact nativeHeat017Init06_formula
    · exact nativeHeat017Init07_formula
    · exact nativeHeat017Init08_formula
    · exact nativeHeat017Init09_formula
    · exact nativeHeat017Init10_formula
    · exact nativeHeat017Init11_formula
    · exact nativeHeat017Init12_formula
    · exact nativeHeat017Init13_formula
    · exact nativeHeat017Init14_formula
    · exact nativeHeat017Init15_formula
    · exact nativeHeat017Init16_formula
    · exact nativeHeat017Init17_formula
    · exact nativeHeat017Init18_formula
    · exact nativeHeat017Init19_formula
    · exact nativeHeat017Init20_formula
theorem nativeHeatStep_hBase_017_Gen : nativeHeatBaseGen 17 = nativeHeat017Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_017_Gen, nativeHeatStep_hInit_017_Gen, nativeHeat017Base_formula]

theorem nativeHeatStep_hFixed_017_Gen : nativeHeatFixedGen 17 = nativeHeat017Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_017_Gen, nativeHeatStep_hFr_017_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat017Fixed01_formula
    · exact nativeHeat017Fixed02_formula
    · exact nativeHeat017Fixed03_formula
    · exact nativeHeat017Fixed04_formula
    · exact nativeHeat017Fixed05_formula
    · exact nativeHeat017Fixed06_formula
    · exact nativeHeat017Fixed07_formula
    · exact nativeHeat017Fixed08_formula
    · exact nativeHeat017Fixed09_formula
    · exact nativeHeat017Fixed10_formula
    · exact nativeHeat017Fixed11_formula
    · exact nativeHeat017Fixed12_formula
    · exact nativeHeat017Fixed13_formula
    · exact nativeHeat017Fixed14_formula
    · exact nativeHeat017Fixed15_formula
    · exact nativeHeat017Fixed16_formula
    · exact nativeHeat017Fixed17_formula
    · exact nativeHeat017Fixed18_formula
    · exact nativeHeat017Fixed19_formula
    · exact nativeHeat017Fixed20_formula

theorem nativeHeatStep_chk_017_Gen :
    nativeHeatPassRootsOk nativeGap018Old nativeHeat017Frames nativeHeat017Coef nativeHeat017Fixed nativeHeat017Base 48 nativeHeat017Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_017_Gen : NativeHeatStepPassNum 17 := by
  refine nativeHeatStepPassNum_of_literals 17 nativeGap018Old nativeHeat017Frames (nativeHeatExpArg nativeGap018Old)
    nativeHeat017Exp nativeHeat017Coef nativeHeat017Fixed nativeHeat017Init nativeHeat017Base nativeHeatStep_hOld_017_Gen
    nativeHeatStep_hFr_017_Gen nativeHeatStep_hArg_017_Gen nativeHeatStep_hExp_017_Gen
    nativeHeatStep_hCoef_017_Gen nativeHeatStep_hFixed_017_Gen
    nativeHeatStep_hInit_017_Gen nativeHeatStep_hBase_017_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_017_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_017_Gen :
    nativeHeatY0Gen 17 = nativeShiftedFrame 1 (min nativeGap018Old.x nativeGap018Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_017_Gen, nativeHeatStep_hInd_017_Gen]

theorem nativeHeatStepFrameNum_017_Gen : NativeHeatStepFrameNum 17 := by
  have h1 := nativeHeatStep_hOld_017_Gen
  have h2 := nativeHeatStep_hInd_017_Gen
  have h3 := nativeHeatStep_hVar_017_Gen
  have h4 := nativeHeatStep_hQm_017_Gen
  have h5 := nativeHeatStep_hQN_017_Gen
  have h6 := nativeHeatStep_hY0_017_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_017_Gen : NativeHeatStepIndivNum 17 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 17 (by norm_num)) = nativeGap018Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_017_Gen]; exact nativeGap018Old_source
  · rw [hc, nativeHeatStep_hInd_017_Gen]; exact nativeGap018Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_017_Gen : nativeHeatY48Gen 17 = nativeHeat017Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_017_Gen, nativeHeatStep_hFr_017_Gen,
    nativeHeatStep_hCoef_017_Gen, nativeHeatStep_hFixed_017_Gen,
    nativeHeatStep_hBase_017_Gen]
  exact nativeHeat017All48

theorem nativeHeatResultGen_017 : nativeHeatResultGen 17 = nativeHeat017Result := by
  rw [← nativeHeat017Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_017_Gen, nativeHeatStep_hY0_017_Gen, nativeHeatStep_hExp_017_Gen,
    nativeHeatStep_hInit_017_Gen, nativeHeatStep_hFixed_017_Gen]

end ASDExplicitGamma.Native

end
