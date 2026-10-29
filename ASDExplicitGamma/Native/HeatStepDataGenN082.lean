module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat082Complete
public import ASDExplicitGamma.Numerics.Native.Gap083Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_082_Gen : nativeHeatOldRowGen 82 = nativeGap083Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_082_Gen : nativeHeatIndividualGen 82 = nativeGap083Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_082_Gen : nativeHeatGenVariance 82 = nativeHeat082Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_082_Gen, nativeHeat082Variance_formula]

theorem nativeHeatStep_hSpec_082_Gen : nativeHeatGenSpectral 82 = nativeHeat082Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_082_Gen, nativeHeat082Variance_formula]

theorem nativeHeatStep_hQm_082_Gen : nativeHeatGenQm 82 = nativeHeat082Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_082_Gen, nativeHeatStep_hSpec_082_Gen,
    nativeHeat082Qm_formula]

theorem nativeHeatStep_hQN_082_Gen : nativeHeatQNGen 82 = nativeHeat082QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_082_Gen, nativeHeat082QN_formula]

theorem nativeHeatStep_hFr_082_Gen : nativeHeatFramesGen 82 = nativeHeat082Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_082_Gen, nativeHeatStep_hInd_082_Gen,
    nativeHeatStep_hVar_082_Gen, nativeHeatStep_hQN_082_Gen, nativeHeat082Frames_formula]

theorem nativeHeatStep_hArg_082_Gen : nativeHeatExpArgGen 82 = nativeHeatExpArg nativeGap083Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_082_Gen]

theorem nativeHeatStep_hExp_082_Gen : nativeHeatExpGen 82 = nativeHeat082Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_082_Gen, nativeHeat082Exp_formula]

theorem nativeHeatStep_hCoef_082_Gen : nativeHeatCoefGen 82 = nativeHeat082Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_082_Gen, nativeHeat082Coef_formula]

theorem nativeHeatStep_hInit_082_Gen : nativeHeatInitGen 82 = nativeHeat082Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_082_Gen, nativeHeatStep_hVar_082_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat082Init00_formula
    · exact nativeHeat082Init01_formula
    · exact nativeHeat082Init02_formula
    · exact nativeHeat082Init03_formula
    · exact nativeHeat082Init04_formula
    · exact nativeHeat082Init05_formula
    · exact nativeHeat082Init06_formula
    · exact nativeHeat082Init07_formula
    · exact nativeHeat082Init08_formula
    · exact nativeHeat082Init09_formula
    · exact nativeHeat082Init10_formula
    · exact nativeHeat082Init11_formula
    · exact nativeHeat082Init12_formula
    · exact nativeHeat082Init13_formula
    · exact nativeHeat082Init14_formula
    · exact nativeHeat082Init15_formula
    · exact nativeHeat082Init16_formula
    · exact nativeHeat082Init17_formula
    · exact nativeHeat082Init18_formula
    · exact nativeHeat082Init19_formula
    · exact nativeHeat082Init20_formula
theorem nativeHeatStep_hBase_082_Gen : nativeHeatBaseGen 82 = nativeHeat082Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_082_Gen, nativeHeatStep_hInit_082_Gen, nativeHeat082Base_formula]

theorem nativeHeatStep_hFixed_082_Gen : nativeHeatFixedGen 82 = nativeHeat082Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_082_Gen, nativeHeatStep_hFr_082_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat082Fixed01_formula
    · exact nativeHeat082Fixed02_formula
    · exact nativeHeat082Fixed03_formula
    · exact nativeHeat082Fixed04_formula
    · exact nativeHeat082Fixed05_formula
    · exact nativeHeat082Fixed06_formula
    · exact nativeHeat082Fixed07_formula
    · exact nativeHeat082Fixed08_formula
    · exact nativeHeat082Fixed09_formula
    · exact nativeHeat082Fixed10_formula
    · exact nativeHeat082Fixed11_formula
    · exact nativeHeat082Fixed12_formula
    · exact nativeHeat082Fixed13_formula
    · exact nativeHeat082Fixed14_formula
    · exact nativeHeat082Fixed15_formula
    · exact nativeHeat082Fixed16_formula
    · exact nativeHeat082Fixed17_formula
    · exact nativeHeat082Fixed18_formula
    · exact nativeHeat082Fixed19_formula
    · exact nativeHeat082Fixed20_formula

theorem nativeHeatStep_chk_082_Gen :
    nativeHeatPassRootsOk nativeGap083Old nativeHeat082Frames nativeHeat082Coef nativeHeat082Fixed nativeHeat082Base 48 nativeHeat082Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_082_Gen : NativeHeatStepPassNum 82 := by
  refine nativeHeatStepPassNum_of_literals 82 nativeGap083Old nativeHeat082Frames (nativeHeatExpArg nativeGap083Old)
    nativeHeat082Exp nativeHeat082Coef nativeHeat082Fixed nativeHeat082Init nativeHeat082Base nativeHeatStep_hOld_082_Gen
    nativeHeatStep_hFr_082_Gen nativeHeatStep_hArg_082_Gen nativeHeatStep_hExp_082_Gen
    nativeHeatStep_hCoef_082_Gen nativeHeatStep_hFixed_082_Gen
    nativeHeatStep_hInit_082_Gen nativeHeatStep_hBase_082_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_082_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_082_Gen :
    nativeHeatY0Gen 82 = nativeShiftedFrame 1 (min nativeGap083Old.x nativeGap083Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_082_Gen, nativeHeatStep_hInd_082_Gen]

theorem nativeHeatStepFrameNum_082_Gen : NativeHeatStepFrameNum 82 := by
  have h1 := nativeHeatStep_hOld_082_Gen
  have h2 := nativeHeatStep_hInd_082_Gen
  have h3 := nativeHeatStep_hVar_082_Gen
  have h4 := nativeHeatStep_hQm_082_Gen
  have h5 := nativeHeatStep_hQN_082_Gen
  have h6 := nativeHeatStep_hY0_082_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_082_Gen : NativeHeatStepIndivNum 82 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 82 (by norm_num)) = nativeGap083Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_082_Gen]; exact nativeGap083Old_source
  · rw [hc, nativeHeatStep_hInd_082_Gen]; exact nativeGap083Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_082_Gen : nativeHeatY48Gen 82 = nativeHeat082Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_082_Gen, nativeHeatStep_hFr_082_Gen,
    nativeHeatStep_hCoef_082_Gen, nativeHeatStep_hFixed_082_Gen,
    nativeHeatStep_hBase_082_Gen]
  exact nativeHeat082All48

theorem nativeHeatResultGen_082 : nativeHeatResultGen 82 = nativeHeat082Result := by
  rw [← nativeHeat082Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_082_Gen, nativeHeatStep_hY0_082_Gen, nativeHeatStep_hExp_082_Gen,
    nativeHeatStep_hInit_082_Gen, nativeHeatStep_hFixed_082_Gen]

end ASDExplicitGamma.Native

end
