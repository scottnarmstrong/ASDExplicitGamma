module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat103Complete
public import ASDExplicitGamma.Numerics.Native.Gap104Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_103_Gen : nativeHeatOldRowGen 103 = nativeGap104Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_103_Gen : nativeHeatIndividualGen 103 = nativeGap104Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_103_Gen : nativeHeatGenVariance 103 = nativeHeat103Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_103_Gen, nativeHeat103Variance_formula]

theorem nativeHeatStep_hSpec_103_Gen : nativeHeatGenSpectral 103 = nativeHeat103Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_103_Gen, nativeHeat103Variance_formula]

theorem nativeHeatStep_hQm_103_Gen : nativeHeatGenQm 103 = nativeHeat103Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_103_Gen, nativeHeatStep_hSpec_103_Gen,
    nativeHeat103Qm_formula]

theorem nativeHeatStep_hQN_103_Gen : nativeHeatQNGen 103 = nativeHeat103QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_103_Gen, nativeHeat103QN_formula]

theorem nativeHeatStep_hFr_103_Gen : nativeHeatFramesGen 103 = nativeHeat103Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_103_Gen, nativeHeatStep_hInd_103_Gen,
    nativeHeatStep_hVar_103_Gen, nativeHeatStep_hQN_103_Gen, nativeHeat103Frames_formula]

theorem nativeHeatStep_hArg_103_Gen : nativeHeatExpArgGen 103 = nativeHeatExpArg nativeGap104Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_103_Gen]

theorem nativeHeatStep_hExp_103_Gen : nativeHeatExpGen 103 = nativeHeat103Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_103_Gen, nativeHeat103Exp_formula]

theorem nativeHeatStep_hCoef_103_Gen : nativeHeatCoefGen 103 = nativeHeat103Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_103_Gen, nativeHeat103Coef_formula]

theorem nativeHeatStep_hInit_103_Gen : nativeHeatInitGen 103 = nativeHeat103Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_103_Gen, nativeHeatStep_hVar_103_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat103Init00_formula
    · exact nativeHeat103Init01_formula
    · exact nativeHeat103Init02_formula
    · exact nativeHeat103Init03_formula
    · exact nativeHeat103Init04_formula
    · exact nativeHeat103Init05_formula
    · exact nativeHeat103Init06_formula
    · exact nativeHeat103Init07_formula
    · exact nativeHeat103Init08_formula
    · exact nativeHeat103Init09_formula
    · exact nativeHeat103Init10_formula
    · exact nativeHeat103Init11_formula
    · exact nativeHeat103Init12_formula
    · exact nativeHeat103Init13_formula
    · exact nativeHeat103Init14_formula
    · exact nativeHeat103Init15_formula
    · exact nativeHeat103Init16_formula
    · exact nativeHeat103Init17_formula
    · exact nativeHeat103Init18_formula
    · exact nativeHeat103Init19_formula
    · exact nativeHeat103Init20_formula
theorem nativeHeatStep_hBase_103_Gen : nativeHeatBaseGen 103 = nativeHeat103Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_103_Gen, nativeHeatStep_hInit_103_Gen, nativeHeat103Base_formula]

theorem nativeHeatStep_hFixed_103_Gen : nativeHeatFixedGen 103 = nativeHeat103Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_103_Gen, nativeHeatStep_hFr_103_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat103Fixed01_formula
    · exact nativeHeat103Fixed02_formula
    · exact nativeHeat103Fixed03_formula
    · exact nativeHeat103Fixed04_formula
    · exact nativeHeat103Fixed05_formula
    · exact nativeHeat103Fixed06_formula
    · exact nativeHeat103Fixed07_formula
    · exact nativeHeat103Fixed08_formula
    · exact nativeHeat103Fixed09_formula
    · exact nativeHeat103Fixed10_formula
    · exact nativeHeat103Fixed11_formula
    · exact nativeHeat103Fixed12_formula
    · exact nativeHeat103Fixed13_formula
    · exact nativeHeat103Fixed14_formula
    · exact nativeHeat103Fixed15_formula
    · exact nativeHeat103Fixed16_formula
    · exact nativeHeat103Fixed17_formula
    · exact nativeHeat103Fixed18_formula
    · exact nativeHeat103Fixed19_formula
    · exact nativeHeat103Fixed20_formula

theorem nativeHeatStep_chk_103_Gen :
    nativeHeatPassRootsOk nativeGap104Old nativeHeat103Frames nativeHeat103Coef nativeHeat103Fixed nativeHeat103Base 48 nativeHeat103Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_103_Gen : NativeHeatStepPassNum 103 := by
  refine nativeHeatStepPassNum_of_literals 103 nativeGap104Old nativeHeat103Frames (nativeHeatExpArg nativeGap104Old)
    nativeHeat103Exp nativeHeat103Coef nativeHeat103Fixed nativeHeat103Init nativeHeat103Base nativeHeatStep_hOld_103_Gen
    nativeHeatStep_hFr_103_Gen nativeHeatStep_hArg_103_Gen nativeHeatStep_hExp_103_Gen
    nativeHeatStep_hCoef_103_Gen nativeHeatStep_hFixed_103_Gen
    nativeHeatStep_hInit_103_Gen nativeHeatStep_hBase_103_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_103_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_103_Gen :
    nativeHeatY0Gen 103 = nativeShiftedFrame 1 (min nativeGap104Old.x nativeGap104Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_103_Gen, nativeHeatStep_hInd_103_Gen]

theorem nativeHeatStepFrameNum_103_Gen : NativeHeatStepFrameNum 103 := by
  have h1 := nativeHeatStep_hOld_103_Gen
  have h2 := nativeHeatStep_hInd_103_Gen
  have h3 := nativeHeatStep_hVar_103_Gen
  have h4 := nativeHeatStep_hQm_103_Gen
  have h5 := nativeHeatStep_hQN_103_Gen
  have h6 := nativeHeatStep_hY0_103_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_103_Gen : NativeHeatStepIndivNum 103 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 103 (by norm_num)) = nativeGap104Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_103_Gen]; exact nativeGap104Old_source
  · rw [hc, nativeHeatStep_hInd_103_Gen]; exact nativeGap104Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_103_Gen : nativeHeatY48Gen 103 = nativeHeat103Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_103_Gen, nativeHeatStep_hFr_103_Gen,
    nativeHeatStep_hCoef_103_Gen, nativeHeatStep_hFixed_103_Gen,
    nativeHeatStep_hBase_103_Gen]
  exact nativeHeat103All48

theorem nativeHeatResultGen_103 : nativeHeatResultGen 103 = nativeHeat103Result := by
  rw [← nativeHeat103Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_103_Gen, nativeHeatStep_hY0_103_Gen, nativeHeatStep_hExp_103_Gen,
    nativeHeatStep_hInit_103_Gen, nativeHeatStep_hFixed_103_Gen]

end ASDExplicitGamma.Native

end
