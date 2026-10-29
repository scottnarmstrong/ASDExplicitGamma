module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat073Complete
public import ASDExplicitGamma.Numerics.Native.Gap074Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_073_Gen : nativeHeatOldRowGen 73 = nativeGap074Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_073_Gen : nativeHeatIndividualGen 73 = nativeGap074Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_073_Gen : nativeHeatGenVariance 73 = nativeHeat073Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_073_Gen, nativeHeat073Variance_formula]

theorem nativeHeatStep_hSpec_073_Gen : nativeHeatGenSpectral 73 = nativeHeat073Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_073_Gen, nativeHeat073Variance_formula]

theorem nativeHeatStep_hQm_073_Gen : nativeHeatGenQm 73 = nativeHeat073Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_073_Gen, nativeHeatStep_hSpec_073_Gen,
    nativeHeat073Qm_formula]

theorem nativeHeatStep_hQN_073_Gen : nativeHeatQNGen 73 = nativeHeat073QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_073_Gen, nativeHeat073QN_formula]

theorem nativeHeatStep_hFr_073_Gen : nativeHeatFramesGen 73 = nativeHeat073Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_073_Gen, nativeHeatStep_hInd_073_Gen,
    nativeHeatStep_hVar_073_Gen, nativeHeatStep_hQN_073_Gen, nativeHeat073Frames_formula]

theorem nativeHeatStep_hArg_073_Gen : nativeHeatExpArgGen 73 = nativeHeatExpArg nativeGap074Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_073_Gen]

theorem nativeHeatStep_hExp_073_Gen : nativeHeatExpGen 73 = nativeHeat073Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_073_Gen, nativeHeat073Exp_formula]

theorem nativeHeatStep_hCoef_073_Gen : nativeHeatCoefGen 73 = nativeHeat073Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_073_Gen, nativeHeat073Coef_formula]

theorem nativeHeatStep_hInit_073_Gen : nativeHeatInitGen 73 = nativeHeat073Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_073_Gen, nativeHeatStep_hVar_073_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat073Init00_formula
    · exact nativeHeat073Init01_formula
    · exact nativeHeat073Init02_formula
    · exact nativeHeat073Init03_formula
    · exact nativeHeat073Init04_formula
    · exact nativeHeat073Init05_formula
    · exact nativeHeat073Init06_formula
    · exact nativeHeat073Init07_formula
    · exact nativeHeat073Init08_formula
    · exact nativeHeat073Init09_formula
    · exact nativeHeat073Init10_formula
    · exact nativeHeat073Init11_formula
    · exact nativeHeat073Init12_formula
    · exact nativeHeat073Init13_formula
    · exact nativeHeat073Init14_formula
    · exact nativeHeat073Init15_formula
    · exact nativeHeat073Init16_formula
    · exact nativeHeat073Init17_formula
    · exact nativeHeat073Init18_formula
    · exact nativeHeat073Init19_formula
    · exact nativeHeat073Init20_formula
theorem nativeHeatStep_hBase_073_Gen : nativeHeatBaseGen 73 = nativeHeat073Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_073_Gen, nativeHeatStep_hInit_073_Gen, nativeHeat073Base_formula]

theorem nativeHeatStep_hFixed_073_Gen : nativeHeatFixedGen 73 = nativeHeat073Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_073_Gen, nativeHeatStep_hFr_073_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat073Fixed01_formula
    · exact nativeHeat073Fixed02_formula
    · exact nativeHeat073Fixed03_formula
    · exact nativeHeat073Fixed04_formula
    · exact nativeHeat073Fixed05_formula
    · exact nativeHeat073Fixed06_formula
    · exact nativeHeat073Fixed07_formula
    · exact nativeHeat073Fixed08_formula
    · exact nativeHeat073Fixed09_formula
    · exact nativeHeat073Fixed10_formula
    · exact nativeHeat073Fixed11_formula
    · exact nativeHeat073Fixed12_formula
    · exact nativeHeat073Fixed13_formula
    · exact nativeHeat073Fixed14_formula
    · exact nativeHeat073Fixed15_formula
    · exact nativeHeat073Fixed16_formula
    · exact nativeHeat073Fixed17_formula
    · exact nativeHeat073Fixed18_formula
    · exact nativeHeat073Fixed19_formula
    · exact nativeHeat073Fixed20_formula

theorem nativeHeatStep_chk_073_Gen :
    nativeHeatPassRootsOk nativeGap074Old nativeHeat073Frames nativeHeat073Coef nativeHeat073Fixed nativeHeat073Base 48 nativeHeat073Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_073_Gen : NativeHeatStepPassNum 73 := by
  refine nativeHeatStepPassNum_of_literals 73 nativeGap074Old nativeHeat073Frames (nativeHeatExpArg nativeGap074Old)
    nativeHeat073Exp nativeHeat073Coef nativeHeat073Fixed nativeHeat073Init nativeHeat073Base nativeHeatStep_hOld_073_Gen
    nativeHeatStep_hFr_073_Gen nativeHeatStep_hArg_073_Gen nativeHeatStep_hExp_073_Gen
    nativeHeatStep_hCoef_073_Gen nativeHeatStep_hFixed_073_Gen
    nativeHeatStep_hInit_073_Gen nativeHeatStep_hBase_073_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_073_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_073_Gen :
    nativeHeatY0Gen 73 = nativeShiftedFrame 1 (min nativeGap074Old.x nativeGap074Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_073_Gen, nativeHeatStep_hInd_073_Gen]

theorem nativeHeatStepFrameNum_073_Gen : NativeHeatStepFrameNum 73 := by
  have h1 := nativeHeatStep_hOld_073_Gen
  have h2 := nativeHeatStep_hInd_073_Gen
  have h3 := nativeHeatStep_hVar_073_Gen
  have h4 := nativeHeatStep_hQm_073_Gen
  have h5 := nativeHeatStep_hQN_073_Gen
  have h6 := nativeHeatStep_hY0_073_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_073_Gen : NativeHeatStepIndivNum 73 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 73 (by norm_num)) = nativeGap074Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_073_Gen]; exact nativeGap074Old_source
  · rw [hc, nativeHeatStep_hInd_073_Gen]; exact nativeGap074Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_073_Gen : nativeHeatY48Gen 73 = nativeHeat073Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_073_Gen, nativeHeatStep_hFr_073_Gen,
    nativeHeatStep_hCoef_073_Gen, nativeHeatStep_hFixed_073_Gen,
    nativeHeatStep_hBase_073_Gen]
  exact nativeHeat073All48

theorem nativeHeatResultGen_073 : nativeHeatResultGen 73 = nativeHeat073Result := by
  rw [← nativeHeat073Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_073_Gen, nativeHeatStep_hY0_073_Gen, nativeHeatStep_hExp_073_Gen,
    nativeHeatStep_hInit_073_Gen, nativeHeatStep_hFixed_073_Gen]

end ASDExplicitGamma.Native

end
