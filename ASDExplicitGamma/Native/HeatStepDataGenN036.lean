module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat036Complete
public import ASDExplicitGamma.Numerics.Native.Gap037Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_036_Gen : nativeHeatOldRowGen 36 = nativeGap037Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_036_Gen : nativeHeatIndividualGen 36 = nativeGap037Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_036_Gen : nativeHeatGenVariance 36 = nativeHeat036Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_036_Gen, nativeHeat036Variance_formula]

theorem nativeHeatStep_hSpec_036_Gen : nativeHeatGenSpectral 36 = nativeHeat036Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_036_Gen, nativeHeat036Variance_formula]

theorem nativeHeatStep_hQm_036_Gen : nativeHeatGenQm 36 = nativeHeat036Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_036_Gen, nativeHeatStep_hSpec_036_Gen,
    nativeHeat036Qm_formula]

theorem nativeHeatStep_hQN_036_Gen : nativeHeatQNGen 36 = nativeHeat036QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_036_Gen, nativeHeat036QN_formula]

theorem nativeHeatStep_hFr_036_Gen : nativeHeatFramesGen 36 = nativeHeat036Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_036_Gen, nativeHeatStep_hInd_036_Gen,
    nativeHeatStep_hVar_036_Gen, nativeHeatStep_hQN_036_Gen, nativeHeat036Frames_formula]

theorem nativeHeatStep_hArg_036_Gen : nativeHeatExpArgGen 36 = nativeHeatExpArg nativeGap037Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_036_Gen]

theorem nativeHeatStep_hExp_036_Gen : nativeHeatExpGen 36 = nativeHeat036Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_036_Gen, nativeHeat036Exp_formula]

theorem nativeHeatStep_hCoef_036_Gen : nativeHeatCoefGen 36 = nativeHeat036Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_036_Gen, nativeHeat036Coef_formula]

theorem nativeHeatStep_hInit_036_Gen : nativeHeatInitGen 36 = nativeHeat036Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_036_Gen, nativeHeatStep_hVar_036_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat036Init00_formula
    · exact nativeHeat036Init01_formula
    · exact nativeHeat036Init02_formula
    · exact nativeHeat036Init03_formula
    · exact nativeHeat036Init04_formula
    · exact nativeHeat036Init05_formula
    · exact nativeHeat036Init06_formula
    · exact nativeHeat036Init07_formula
    · exact nativeHeat036Init08_formula
    · exact nativeHeat036Init09_formula
    · exact nativeHeat036Init10_formula
    · exact nativeHeat036Init11_formula
    · exact nativeHeat036Init12_formula
    · exact nativeHeat036Init13_formula
    · exact nativeHeat036Init14_formula
    · exact nativeHeat036Init15_formula
    · exact nativeHeat036Init16_formula
    · exact nativeHeat036Init17_formula
    · exact nativeHeat036Init18_formula
    · exact nativeHeat036Init19_formula
    · exact nativeHeat036Init20_formula
theorem nativeHeatStep_hBase_036_Gen : nativeHeatBaseGen 36 = nativeHeat036Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_036_Gen, nativeHeatStep_hInit_036_Gen, nativeHeat036Base_formula]

theorem nativeHeatStep_hFixed_036_Gen : nativeHeatFixedGen 36 = nativeHeat036Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_036_Gen, nativeHeatStep_hFr_036_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat036Fixed01_formula
    · exact nativeHeat036Fixed02_formula
    · exact nativeHeat036Fixed03_formula
    · exact nativeHeat036Fixed04_formula
    · exact nativeHeat036Fixed05_formula
    · exact nativeHeat036Fixed06_formula
    · exact nativeHeat036Fixed07_formula
    · exact nativeHeat036Fixed08_formula
    · exact nativeHeat036Fixed09_formula
    · exact nativeHeat036Fixed10_formula
    · exact nativeHeat036Fixed11_formula
    · exact nativeHeat036Fixed12_formula
    · exact nativeHeat036Fixed13_formula
    · exact nativeHeat036Fixed14_formula
    · exact nativeHeat036Fixed15_formula
    · exact nativeHeat036Fixed16_formula
    · exact nativeHeat036Fixed17_formula
    · exact nativeHeat036Fixed18_formula
    · exact nativeHeat036Fixed19_formula
    · exact nativeHeat036Fixed20_formula

theorem nativeHeatStep_chk_036_Gen :
    nativeHeatPassRootsOk nativeGap037Old nativeHeat036Frames nativeHeat036Coef nativeHeat036Fixed nativeHeat036Base 48 nativeHeat036Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_036_Gen : NativeHeatStepPassNum 36 := by
  refine nativeHeatStepPassNum_of_literals 36 nativeGap037Old nativeHeat036Frames (nativeHeatExpArg nativeGap037Old)
    nativeHeat036Exp nativeHeat036Coef nativeHeat036Fixed nativeHeat036Init nativeHeat036Base nativeHeatStep_hOld_036_Gen
    nativeHeatStep_hFr_036_Gen nativeHeatStep_hArg_036_Gen nativeHeatStep_hExp_036_Gen
    nativeHeatStep_hCoef_036_Gen nativeHeatStep_hFixed_036_Gen
    nativeHeatStep_hInit_036_Gen nativeHeatStep_hBase_036_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_036_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_036_Gen :
    nativeHeatY0Gen 36 = nativeShiftedFrame 1 (min nativeGap037Old.x nativeGap037Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_036_Gen, nativeHeatStep_hInd_036_Gen]

theorem nativeHeatStepFrameNum_036_Gen : NativeHeatStepFrameNum 36 := by
  have h1 := nativeHeatStep_hOld_036_Gen
  have h2 := nativeHeatStep_hInd_036_Gen
  have h3 := nativeHeatStep_hVar_036_Gen
  have h4 := nativeHeatStep_hQm_036_Gen
  have h5 := nativeHeatStep_hQN_036_Gen
  have h6 := nativeHeatStep_hY0_036_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_036_Gen : NativeHeatStepIndivNum 36 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 36 (by norm_num)) = nativeGap037Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_036_Gen]; exact nativeGap037Old_source
  · rw [hc, nativeHeatStep_hInd_036_Gen]; exact nativeGap037Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_036_Gen : nativeHeatY48Gen 36 = nativeHeat036Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_036_Gen, nativeHeatStep_hFr_036_Gen,
    nativeHeatStep_hCoef_036_Gen, nativeHeatStep_hFixed_036_Gen,
    nativeHeatStep_hBase_036_Gen]
  exact nativeHeat036All48

theorem nativeHeatResultGen_036 : nativeHeatResultGen 36 = nativeHeat036Result := by
  rw [← nativeHeat036Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_036_Gen, nativeHeatStep_hY0_036_Gen, nativeHeatStep_hExp_036_Gen,
    nativeHeatStep_hInit_036_Gen, nativeHeatStep_hFixed_036_Gen]

end ASDExplicitGamma.Native

end
