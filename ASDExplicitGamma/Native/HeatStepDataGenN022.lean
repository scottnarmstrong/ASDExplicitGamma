module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat022Complete
public import ASDExplicitGamma.Numerics.Native.Gap023Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_022_Gen : nativeHeatOldRowGen 22 = nativeGap023Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_022_Gen : nativeHeatIndividualGen 22 = nativeGap023Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_022_Gen : nativeHeatGenVariance 22 = nativeHeat022Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_022_Gen, nativeHeat022Variance_formula]

theorem nativeHeatStep_hSpec_022_Gen : nativeHeatGenSpectral 22 = nativeHeat022Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_022_Gen, nativeHeat022Variance_formula]

theorem nativeHeatStep_hQm_022_Gen : nativeHeatGenQm 22 = nativeHeat022Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_022_Gen, nativeHeatStep_hSpec_022_Gen,
    nativeHeat022Qm_formula]

theorem nativeHeatStep_hQN_022_Gen : nativeHeatQNGen 22 = nativeHeat022QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_022_Gen, nativeHeat022QN_formula]

theorem nativeHeatStep_hFr_022_Gen : nativeHeatFramesGen 22 = nativeHeat022Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_022_Gen, nativeHeatStep_hInd_022_Gen,
    nativeHeatStep_hVar_022_Gen, nativeHeatStep_hQN_022_Gen, nativeHeat022Frames_formula]

theorem nativeHeatStep_hArg_022_Gen : nativeHeatExpArgGen 22 = nativeHeatExpArg nativeGap023Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_022_Gen]

theorem nativeHeatStep_hExp_022_Gen : nativeHeatExpGen 22 = nativeHeat022Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_022_Gen, nativeHeat022Exp_formula]

theorem nativeHeatStep_hCoef_022_Gen : nativeHeatCoefGen 22 = nativeHeat022Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_022_Gen, nativeHeat022Coef_formula]

theorem nativeHeatStep_hInit_022_Gen : nativeHeatInitGen 22 = nativeHeat022Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_022_Gen, nativeHeatStep_hVar_022_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat022Init00_formula
    · exact nativeHeat022Init01_formula
    · exact nativeHeat022Init02_formula
    · exact nativeHeat022Init03_formula
    · exact nativeHeat022Init04_formula
    · exact nativeHeat022Init05_formula
    · exact nativeHeat022Init06_formula
    · exact nativeHeat022Init07_formula
    · exact nativeHeat022Init08_formula
    · exact nativeHeat022Init09_formula
    · exact nativeHeat022Init10_formula
    · exact nativeHeat022Init11_formula
    · exact nativeHeat022Init12_formula
    · exact nativeHeat022Init13_formula
    · exact nativeHeat022Init14_formula
    · exact nativeHeat022Init15_formula
    · exact nativeHeat022Init16_formula
    · exact nativeHeat022Init17_formula
    · exact nativeHeat022Init18_formula
    · exact nativeHeat022Init19_formula
    · exact nativeHeat022Init20_formula
theorem nativeHeatStep_hBase_022_Gen : nativeHeatBaseGen 22 = nativeHeat022Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_022_Gen, nativeHeatStep_hInit_022_Gen, nativeHeat022Base_formula]

theorem nativeHeatStep_hFixed_022_Gen : nativeHeatFixedGen 22 = nativeHeat022Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_022_Gen, nativeHeatStep_hFr_022_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat022Fixed01_formula
    · exact nativeHeat022Fixed02_formula
    · exact nativeHeat022Fixed03_formula
    · exact nativeHeat022Fixed04_formula
    · exact nativeHeat022Fixed05_formula
    · exact nativeHeat022Fixed06_formula
    · exact nativeHeat022Fixed07_formula
    · exact nativeHeat022Fixed08_formula
    · exact nativeHeat022Fixed09_formula
    · exact nativeHeat022Fixed10_formula
    · exact nativeHeat022Fixed11_formula
    · exact nativeHeat022Fixed12_formula
    · exact nativeHeat022Fixed13_formula
    · exact nativeHeat022Fixed14_formula
    · exact nativeHeat022Fixed15_formula
    · exact nativeHeat022Fixed16_formula
    · exact nativeHeat022Fixed17_formula
    · exact nativeHeat022Fixed18_formula
    · exact nativeHeat022Fixed19_formula
    · exact nativeHeat022Fixed20_formula

theorem nativeHeatStep_chk_022_Gen :
    nativeHeatPassRootsOk nativeGap023Old nativeHeat022Frames nativeHeat022Coef nativeHeat022Fixed nativeHeat022Base 48 nativeHeat022Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_022_Gen : NativeHeatStepPassNum 22 := by
  refine nativeHeatStepPassNum_of_literals 22 nativeGap023Old nativeHeat022Frames (nativeHeatExpArg nativeGap023Old)
    nativeHeat022Exp nativeHeat022Coef nativeHeat022Fixed nativeHeat022Init nativeHeat022Base nativeHeatStep_hOld_022_Gen
    nativeHeatStep_hFr_022_Gen nativeHeatStep_hArg_022_Gen nativeHeatStep_hExp_022_Gen
    nativeHeatStep_hCoef_022_Gen nativeHeatStep_hFixed_022_Gen
    nativeHeatStep_hInit_022_Gen nativeHeatStep_hBase_022_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_022_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_022_Gen :
    nativeHeatY0Gen 22 = nativeShiftedFrame 1 (min nativeGap023Old.x nativeGap023Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_022_Gen, nativeHeatStep_hInd_022_Gen]

theorem nativeHeatStepFrameNum_022_Gen : NativeHeatStepFrameNum 22 := by
  have h1 := nativeHeatStep_hOld_022_Gen
  have h2 := nativeHeatStep_hInd_022_Gen
  have h3 := nativeHeatStep_hVar_022_Gen
  have h4 := nativeHeatStep_hQm_022_Gen
  have h5 := nativeHeatStep_hQN_022_Gen
  have h6 := nativeHeatStep_hY0_022_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_022_Gen : NativeHeatStepIndivNum 22 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 22 (by norm_num)) = nativeGap023Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_022_Gen]; exact nativeGap023Old_source
  · rw [hc, nativeHeatStep_hInd_022_Gen]; exact nativeGap023Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_022_Gen : nativeHeatY48Gen 22 = nativeHeat022Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_022_Gen, nativeHeatStep_hFr_022_Gen,
    nativeHeatStep_hCoef_022_Gen, nativeHeatStep_hFixed_022_Gen,
    nativeHeatStep_hBase_022_Gen]
  exact nativeHeat022All48

theorem nativeHeatResultGen_022 : nativeHeatResultGen 22 = nativeHeat022Result := by
  rw [← nativeHeat022Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_022_Gen, nativeHeatStep_hY0_022_Gen, nativeHeatStep_hExp_022_Gen,
    nativeHeatStep_hInit_022_Gen, nativeHeatStep_hFixed_022_Gen]

end ASDExplicitGamma.Native

end
