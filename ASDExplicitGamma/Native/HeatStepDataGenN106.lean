module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat106Complete
public import ASDExplicitGamma.Numerics.Native.Gap107Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_106_Gen : nativeHeatOldRowGen 106 = nativeGap107Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_106_Gen : nativeHeatIndividualGen 106 = nativeGap107Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_106_Gen : nativeHeatGenVariance 106 = nativeHeat106Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_106_Gen, nativeHeat106Variance_formula]

theorem nativeHeatStep_hSpec_106_Gen : nativeHeatGenSpectral 106 = nativeHeat106Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_106_Gen, nativeHeat106Variance_formula]

theorem nativeHeatStep_hQm_106_Gen : nativeHeatGenQm 106 = nativeHeat106Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_106_Gen, nativeHeatStep_hSpec_106_Gen,
    nativeHeat106Qm_formula]

theorem nativeHeatStep_hQN_106_Gen : nativeHeatQNGen 106 = nativeHeat106QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_106_Gen, nativeHeat106QN_formula]

theorem nativeHeatStep_hFr_106_Gen : nativeHeatFramesGen 106 = nativeHeat106Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_106_Gen, nativeHeatStep_hInd_106_Gen,
    nativeHeatStep_hVar_106_Gen, nativeHeatStep_hQN_106_Gen, nativeHeat106Frames_formula]

theorem nativeHeatStep_hArg_106_Gen : nativeHeatExpArgGen 106 = nativeHeatExpArg nativeGap107Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_106_Gen]

theorem nativeHeatStep_hExp_106_Gen : nativeHeatExpGen 106 = nativeHeat106Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_106_Gen, nativeHeat106Exp_formula]

theorem nativeHeatStep_hCoef_106_Gen : nativeHeatCoefGen 106 = nativeHeat106Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_106_Gen, nativeHeat106Coef_formula]

theorem nativeHeatStep_hInit_106_Gen : nativeHeatInitGen 106 = nativeHeat106Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_106_Gen, nativeHeatStep_hVar_106_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat106Init00_formula
    · exact nativeHeat106Init01_formula
    · exact nativeHeat106Init02_formula
    · exact nativeHeat106Init03_formula
    · exact nativeHeat106Init04_formula
    · exact nativeHeat106Init05_formula
    · exact nativeHeat106Init06_formula
    · exact nativeHeat106Init07_formula
    · exact nativeHeat106Init08_formula
    · exact nativeHeat106Init09_formula
    · exact nativeHeat106Init10_formula
    · exact nativeHeat106Init11_formula
    · exact nativeHeat106Init12_formula
    · exact nativeHeat106Init13_formula
    · exact nativeHeat106Init14_formula
    · exact nativeHeat106Init15_formula
    · exact nativeHeat106Init16_formula
    · exact nativeHeat106Init17_formula
    · exact nativeHeat106Init18_formula
    · exact nativeHeat106Init19_formula
    · exact nativeHeat106Init20_formula
theorem nativeHeatStep_hBase_106_Gen : nativeHeatBaseGen 106 = nativeHeat106Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_106_Gen, nativeHeatStep_hInit_106_Gen, nativeHeat106Base_formula]

theorem nativeHeatStep_hFixed_106_Gen : nativeHeatFixedGen 106 = nativeHeat106Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_106_Gen, nativeHeatStep_hFr_106_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat106Fixed01_formula
    · exact nativeHeat106Fixed02_formula
    · exact nativeHeat106Fixed03_formula
    · exact nativeHeat106Fixed04_formula
    · exact nativeHeat106Fixed05_formula
    · exact nativeHeat106Fixed06_formula
    · exact nativeHeat106Fixed07_formula
    · exact nativeHeat106Fixed08_formula
    · exact nativeHeat106Fixed09_formula
    · exact nativeHeat106Fixed10_formula
    · exact nativeHeat106Fixed11_formula
    · exact nativeHeat106Fixed12_formula
    · exact nativeHeat106Fixed13_formula
    · exact nativeHeat106Fixed14_formula
    · exact nativeHeat106Fixed15_formula
    · exact nativeHeat106Fixed16_formula
    · exact nativeHeat106Fixed17_formula
    · exact nativeHeat106Fixed18_formula
    · exact nativeHeat106Fixed19_formula
    · exact nativeHeat106Fixed20_formula

theorem nativeHeatStep_chk_106_Gen :
    nativeHeatPassRootsOk nativeGap107Old nativeHeat106Frames nativeHeat106Coef nativeHeat106Fixed nativeHeat106Base 48 nativeHeat106Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_106_Gen : NativeHeatStepPassNum 106 := by
  refine nativeHeatStepPassNum_of_literals 106 nativeGap107Old nativeHeat106Frames (nativeHeatExpArg nativeGap107Old)
    nativeHeat106Exp nativeHeat106Coef nativeHeat106Fixed nativeHeat106Init nativeHeat106Base nativeHeatStep_hOld_106_Gen
    nativeHeatStep_hFr_106_Gen nativeHeatStep_hArg_106_Gen nativeHeatStep_hExp_106_Gen
    nativeHeatStep_hCoef_106_Gen nativeHeatStep_hFixed_106_Gen
    nativeHeatStep_hInit_106_Gen nativeHeatStep_hBase_106_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_106_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_106_Gen :
    nativeHeatY0Gen 106 = nativeShiftedFrame 1 (min nativeGap107Old.x nativeGap107Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_106_Gen, nativeHeatStep_hInd_106_Gen]

theorem nativeHeatStepFrameNum_106_Gen : NativeHeatStepFrameNum 106 := by
  have h1 := nativeHeatStep_hOld_106_Gen
  have h2 := nativeHeatStep_hInd_106_Gen
  have h3 := nativeHeatStep_hVar_106_Gen
  have h4 := nativeHeatStep_hQm_106_Gen
  have h5 := nativeHeatStep_hQN_106_Gen
  have h6 := nativeHeatStep_hY0_106_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_106_Gen : NativeHeatStepIndivNum 106 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 106 (by norm_num)) = nativeGap107Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_106_Gen]; exact nativeGap107Old_source
  · rw [hc, nativeHeatStep_hInd_106_Gen]; exact nativeGap107Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_106_Gen : nativeHeatY48Gen 106 = nativeHeat106Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_106_Gen, nativeHeatStep_hFr_106_Gen,
    nativeHeatStep_hCoef_106_Gen, nativeHeatStep_hFixed_106_Gen,
    nativeHeatStep_hBase_106_Gen]
  exact nativeHeat106All48

theorem nativeHeatResultGen_106 : nativeHeatResultGen 106 = nativeHeat106Result := by
  rw [← nativeHeat106Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_106_Gen, nativeHeatStep_hY0_106_Gen, nativeHeatStep_hExp_106_Gen,
    nativeHeatStep_hInit_106_Gen, nativeHeatStep_hFixed_106_Gen]

end ASDExplicitGamma.Native

end
