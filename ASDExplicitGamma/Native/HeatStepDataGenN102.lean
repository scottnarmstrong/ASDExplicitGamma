module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat102Complete
public import ASDExplicitGamma.Numerics.Native.Gap103Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_102_Gen : nativeHeatOldRowGen 102 = nativeGap103Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_102_Gen : nativeHeatIndividualGen 102 = nativeGap103Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_102_Gen : nativeHeatGenVariance 102 = nativeHeat102Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_102_Gen, nativeHeat102Variance_formula]

theorem nativeHeatStep_hSpec_102_Gen : nativeHeatGenSpectral 102 = nativeHeat102Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_102_Gen, nativeHeat102Variance_formula]

theorem nativeHeatStep_hQm_102_Gen : nativeHeatGenQm 102 = nativeHeat102Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_102_Gen, nativeHeatStep_hSpec_102_Gen,
    nativeHeat102Qm_formula]

theorem nativeHeatStep_hQN_102_Gen : nativeHeatQNGen 102 = nativeHeat102QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_102_Gen, nativeHeat102QN_formula]

theorem nativeHeatStep_hFr_102_Gen : nativeHeatFramesGen 102 = nativeHeat102Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_102_Gen, nativeHeatStep_hInd_102_Gen,
    nativeHeatStep_hVar_102_Gen, nativeHeatStep_hQN_102_Gen, nativeHeat102Frames_formula]

theorem nativeHeatStep_hArg_102_Gen : nativeHeatExpArgGen 102 = nativeHeatExpArg nativeGap103Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_102_Gen]

theorem nativeHeatStep_hExp_102_Gen : nativeHeatExpGen 102 = nativeHeat102Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_102_Gen, nativeHeat102Exp_formula]

theorem nativeHeatStep_hCoef_102_Gen : nativeHeatCoefGen 102 = nativeHeat102Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_102_Gen, nativeHeat102Coef_formula]

theorem nativeHeatStep_hInit_102_Gen : nativeHeatInitGen 102 = nativeHeat102Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_102_Gen, nativeHeatStep_hVar_102_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat102Init00_formula
    · exact nativeHeat102Init01_formula
    · exact nativeHeat102Init02_formula
    · exact nativeHeat102Init03_formula
    · exact nativeHeat102Init04_formula
    · exact nativeHeat102Init05_formula
    · exact nativeHeat102Init06_formula
    · exact nativeHeat102Init07_formula
    · exact nativeHeat102Init08_formula
    · exact nativeHeat102Init09_formula
    · exact nativeHeat102Init10_formula
    · exact nativeHeat102Init11_formula
    · exact nativeHeat102Init12_formula
    · exact nativeHeat102Init13_formula
    · exact nativeHeat102Init14_formula
    · exact nativeHeat102Init15_formula
    · exact nativeHeat102Init16_formula
    · exact nativeHeat102Init17_formula
    · exact nativeHeat102Init18_formula
    · exact nativeHeat102Init19_formula
    · exact nativeHeat102Init20_formula
theorem nativeHeatStep_hBase_102_Gen : nativeHeatBaseGen 102 = nativeHeat102Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_102_Gen, nativeHeatStep_hInit_102_Gen, nativeHeat102Base_formula]

theorem nativeHeatStep_hFixed_102_Gen : nativeHeatFixedGen 102 = nativeHeat102Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_102_Gen, nativeHeatStep_hFr_102_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat102Fixed01_formula
    · exact nativeHeat102Fixed02_formula
    · exact nativeHeat102Fixed03_formula
    · exact nativeHeat102Fixed04_formula
    · exact nativeHeat102Fixed05_formula
    · exact nativeHeat102Fixed06_formula
    · exact nativeHeat102Fixed07_formula
    · exact nativeHeat102Fixed08_formula
    · exact nativeHeat102Fixed09_formula
    · exact nativeHeat102Fixed10_formula
    · exact nativeHeat102Fixed11_formula
    · exact nativeHeat102Fixed12_formula
    · exact nativeHeat102Fixed13_formula
    · exact nativeHeat102Fixed14_formula
    · exact nativeHeat102Fixed15_formula
    · exact nativeHeat102Fixed16_formula
    · exact nativeHeat102Fixed17_formula
    · exact nativeHeat102Fixed18_formula
    · exact nativeHeat102Fixed19_formula
    · exact nativeHeat102Fixed20_formula

theorem nativeHeatStep_chk_102_Gen :
    nativeHeatPassRootsOk nativeGap103Old nativeHeat102Frames nativeHeat102Coef nativeHeat102Fixed nativeHeat102Base 48 nativeHeat102Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_102_Gen : NativeHeatStepPassNum 102 := by
  refine nativeHeatStepPassNum_of_literals 102 nativeGap103Old nativeHeat102Frames (nativeHeatExpArg nativeGap103Old)
    nativeHeat102Exp nativeHeat102Coef nativeHeat102Fixed nativeHeat102Init nativeHeat102Base nativeHeatStep_hOld_102_Gen
    nativeHeatStep_hFr_102_Gen nativeHeatStep_hArg_102_Gen nativeHeatStep_hExp_102_Gen
    nativeHeatStep_hCoef_102_Gen nativeHeatStep_hFixed_102_Gen
    nativeHeatStep_hInit_102_Gen nativeHeatStep_hBase_102_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_102_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_102_Gen :
    nativeHeatY0Gen 102 = nativeShiftedFrame 1 (min nativeGap103Old.x nativeGap103Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_102_Gen, nativeHeatStep_hInd_102_Gen]

theorem nativeHeatStepFrameNum_102_Gen : NativeHeatStepFrameNum 102 := by
  have h1 := nativeHeatStep_hOld_102_Gen
  have h2 := nativeHeatStep_hInd_102_Gen
  have h3 := nativeHeatStep_hVar_102_Gen
  have h4 := nativeHeatStep_hQm_102_Gen
  have h5 := nativeHeatStep_hQN_102_Gen
  have h6 := nativeHeatStep_hY0_102_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_102_Gen : NativeHeatStepIndivNum 102 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 102 (by norm_num)) = nativeGap103Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_102_Gen]; exact nativeGap103Old_source
  · rw [hc, nativeHeatStep_hInd_102_Gen]; exact nativeGap103Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_102_Gen : nativeHeatY48Gen 102 = nativeHeat102Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_102_Gen, nativeHeatStep_hFr_102_Gen,
    nativeHeatStep_hCoef_102_Gen, nativeHeatStep_hFixed_102_Gen,
    nativeHeatStep_hBase_102_Gen]
  exact nativeHeat102All48

theorem nativeHeatResultGen_102 : nativeHeatResultGen 102 = nativeHeat102Result := by
  rw [← nativeHeat102Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_102_Gen, nativeHeatStep_hY0_102_Gen, nativeHeatStep_hExp_102_Gen,
    nativeHeatStep_hInit_102_Gen, nativeHeatStep_hFixed_102_Gen]

end ASDExplicitGamma.Native

end
