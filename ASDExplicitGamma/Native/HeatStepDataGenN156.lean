module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat156Complete
public import ASDExplicitGamma.Numerics.Native.Gap157Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_156_Gen : nativeHeatOldRowGen 156 = nativeGap157Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_156_Gen : nativeHeatIndividualGen 156 = nativeGap157Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_156_Gen : nativeHeatGenVariance 156 = nativeHeat156Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_156_Gen, nativeHeat156Variance_formula]

theorem nativeHeatStep_hSpec_156_Gen : nativeHeatGenSpectral 156 = nativeHeat156Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_156_Gen, nativeHeat156Variance_formula]

theorem nativeHeatStep_hQm_156_Gen : nativeHeatGenQm 156 = nativeHeat156Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_156_Gen, nativeHeatStep_hSpec_156_Gen,
    nativeHeat156Qm_formula]

theorem nativeHeatStep_hQN_156_Gen : nativeHeatQNGen 156 = nativeHeat156QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_156_Gen, nativeHeat156QN_formula]

theorem nativeHeatStep_hFr_156_Gen : nativeHeatFramesGen 156 = nativeHeat156Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_156_Gen, nativeHeatStep_hInd_156_Gen,
    nativeHeatStep_hVar_156_Gen, nativeHeatStep_hQN_156_Gen, nativeHeat156Frames_formula]

theorem nativeHeatStep_hArg_156_Gen : nativeHeatExpArgGen 156 = nativeHeatExpArg nativeGap157Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_156_Gen]

theorem nativeHeatStep_hExp_156_Gen : nativeHeatExpGen 156 = nativeHeat156Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_156_Gen, nativeHeat156Exp_formula]

theorem nativeHeatStep_hCoef_156_Gen : nativeHeatCoefGen 156 = nativeHeat156Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_156_Gen, nativeHeat156Coef_formula]

theorem nativeHeatStep_hInit_156_Gen : nativeHeatInitGen 156 = nativeHeat156Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_156_Gen, nativeHeatStep_hVar_156_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat156Init00_formula
    · exact nativeHeat156Init01_formula
    · exact nativeHeat156Init02_formula
    · exact nativeHeat156Init03_formula
    · exact nativeHeat156Init04_formula
    · exact nativeHeat156Init05_formula
    · exact nativeHeat156Init06_formula
    · exact nativeHeat156Init07_formula
    · exact nativeHeat156Init08_formula
    · exact nativeHeat156Init09_formula
    · exact nativeHeat156Init10_formula
    · exact nativeHeat156Init11_formula
    · exact nativeHeat156Init12_formula
    · exact nativeHeat156Init13_formula
    · exact nativeHeat156Init14_formula
    · exact nativeHeat156Init15_formula
    · exact nativeHeat156Init16_formula
    · exact nativeHeat156Init17_formula
    · exact nativeHeat156Init18_formula
    · exact nativeHeat156Init19_formula
    · exact nativeHeat156Init20_formula
theorem nativeHeatStep_hBase_156_Gen : nativeHeatBaseGen 156 = nativeHeat156Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_156_Gen, nativeHeatStep_hInit_156_Gen, nativeHeat156Base_formula]

theorem nativeHeatStep_hFixed_156_Gen : nativeHeatFixedGen 156 = nativeHeat156Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_156_Gen, nativeHeatStep_hFr_156_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat156Fixed01_formula
    · exact nativeHeat156Fixed02_formula
    · exact nativeHeat156Fixed03_formula
    · exact nativeHeat156Fixed04_formula
    · exact nativeHeat156Fixed05_formula
    · exact nativeHeat156Fixed06_formula
    · exact nativeHeat156Fixed07_formula
    · exact nativeHeat156Fixed08_formula
    · exact nativeHeat156Fixed09_formula
    · exact nativeHeat156Fixed10_formula
    · exact nativeHeat156Fixed11_formula
    · exact nativeHeat156Fixed12_formula
    · exact nativeHeat156Fixed13_formula
    · exact nativeHeat156Fixed14_formula
    · exact nativeHeat156Fixed15_formula
    · exact nativeHeat156Fixed16_formula
    · exact nativeHeat156Fixed17_formula
    · exact nativeHeat156Fixed18_formula
    · exact nativeHeat156Fixed19_formula
    · exact nativeHeat156Fixed20_formula

theorem nativeHeatStep_chk_156_Gen :
    nativeHeatPassRootsOk nativeGap157Old nativeHeat156Frames nativeHeat156Coef nativeHeat156Fixed nativeHeat156Base 48 nativeHeat156Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_156_Gen : NativeHeatStepPassNum 156 := by
  refine nativeHeatStepPassNum_of_literals 156 nativeGap157Old nativeHeat156Frames (nativeHeatExpArg nativeGap157Old)
    nativeHeat156Exp nativeHeat156Coef nativeHeat156Fixed nativeHeat156Init nativeHeat156Base nativeHeatStep_hOld_156_Gen
    nativeHeatStep_hFr_156_Gen nativeHeatStep_hArg_156_Gen nativeHeatStep_hExp_156_Gen
    nativeHeatStep_hCoef_156_Gen nativeHeatStep_hFixed_156_Gen
    nativeHeatStep_hInit_156_Gen nativeHeatStep_hBase_156_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_156_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_156_Gen :
    nativeHeatY0Gen 156 = nativeShiftedFrame 1 (min nativeGap157Old.x nativeGap157Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_156_Gen, nativeHeatStep_hInd_156_Gen]

theorem nativeHeatStepFrameNum_156_Gen : NativeHeatStepFrameNum 156 := by
  have h1 := nativeHeatStep_hOld_156_Gen
  have h2 := nativeHeatStep_hInd_156_Gen
  have h3 := nativeHeatStep_hVar_156_Gen
  have h4 := nativeHeatStep_hQm_156_Gen
  have h5 := nativeHeatStep_hQN_156_Gen
  have h6 := nativeHeatStep_hY0_156_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_156_Gen : NativeHeatStepIndivNum 156 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 156 (by norm_num)) = nativeGap157Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_156_Gen]; exact nativeGap157Old_source
  · rw [hc, nativeHeatStep_hInd_156_Gen]; exact nativeGap157Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_156_Gen : nativeHeatY48Gen 156 = nativeHeat156Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_156_Gen, nativeHeatStep_hFr_156_Gen,
    nativeHeatStep_hCoef_156_Gen, nativeHeatStep_hFixed_156_Gen,
    nativeHeatStep_hBase_156_Gen]
  exact nativeHeat156All48

theorem nativeHeatResultGen_156 : nativeHeatResultGen 156 = nativeHeat156Result := by
  rw [← nativeHeat156Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_156_Gen, nativeHeatStep_hY0_156_Gen, nativeHeatStep_hExp_156_Gen,
    nativeHeatStep_hInit_156_Gen, nativeHeatStep_hFixed_156_Gen]

end ASDExplicitGamma.Native

end
