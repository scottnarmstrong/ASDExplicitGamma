module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat134Complete
public import ASDExplicitGamma.Numerics.Native.Gap135Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_134_Gen : nativeHeatOldRowGen 134 = nativeGap135Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_134_Gen : nativeHeatIndividualGen 134 = nativeGap135Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_134_Gen : nativeHeatGenVariance 134 = nativeHeat134Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_134_Gen, nativeHeat134Variance_formula]

theorem nativeHeatStep_hSpec_134_Gen : nativeHeatGenSpectral 134 = nativeHeat134Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_134_Gen, nativeHeat134Variance_formula]

theorem nativeHeatStep_hQm_134_Gen : nativeHeatGenQm 134 = nativeHeat134Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_134_Gen, nativeHeatStep_hSpec_134_Gen,
    nativeHeat134Qm_formula]

theorem nativeHeatStep_hQN_134_Gen : nativeHeatQNGen 134 = nativeHeat134QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_134_Gen, nativeHeat134QN_formula]

theorem nativeHeatStep_hFr_134_Gen : nativeHeatFramesGen 134 = nativeHeat134Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_134_Gen, nativeHeatStep_hInd_134_Gen,
    nativeHeatStep_hVar_134_Gen, nativeHeatStep_hQN_134_Gen, nativeHeat134Frames_formula]

theorem nativeHeatStep_hArg_134_Gen : nativeHeatExpArgGen 134 = nativeHeatExpArg nativeGap135Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_134_Gen]

theorem nativeHeatStep_hExp_134_Gen : nativeHeatExpGen 134 = nativeHeat134Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_134_Gen, nativeHeat134Exp_formula]

theorem nativeHeatStep_hCoef_134_Gen : nativeHeatCoefGen 134 = nativeHeat134Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_134_Gen, nativeHeat134Coef_formula]

theorem nativeHeatStep_hInit_134_Gen : nativeHeatInitGen 134 = nativeHeat134Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_134_Gen, nativeHeatStep_hVar_134_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat134Init00_formula
    · exact nativeHeat134Init01_formula
    · exact nativeHeat134Init02_formula
    · exact nativeHeat134Init03_formula
    · exact nativeHeat134Init04_formula
    · exact nativeHeat134Init05_formula
    · exact nativeHeat134Init06_formula
    · exact nativeHeat134Init07_formula
    · exact nativeHeat134Init08_formula
    · exact nativeHeat134Init09_formula
    · exact nativeHeat134Init10_formula
    · exact nativeHeat134Init11_formula
    · exact nativeHeat134Init12_formula
    · exact nativeHeat134Init13_formula
    · exact nativeHeat134Init14_formula
    · exact nativeHeat134Init15_formula
    · exact nativeHeat134Init16_formula
    · exact nativeHeat134Init17_formula
    · exact nativeHeat134Init18_formula
    · exact nativeHeat134Init19_formula
    · exact nativeHeat134Init20_formula
theorem nativeHeatStep_hBase_134_Gen : nativeHeatBaseGen 134 = nativeHeat134Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_134_Gen, nativeHeatStep_hInit_134_Gen, nativeHeat134Base_formula]

theorem nativeHeatStep_hFixed_134_Gen : nativeHeatFixedGen 134 = nativeHeat134Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_134_Gen, nativeHeatStep_hFr_134_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat134Fixed01_formula
    · exact nativeHeat134Fixed02_formula
    · exact nativeHeat134Fixed03_formula
    · exact nativeHeat134Fixed04_formula
    · exact nativeHeat134Fixed05_formula
    · exact nativeHeat134Fixed06_formula
    · exact nativeHeat134Fixed07_formula
    · exact nativeHeat134Fixed08_formula
    · exact nativeHeat134Fixed09_formula
    · exact nativeHeat134Fixed10_formula
    · exact nativeHeat134Fixed11_formula
    · exact nativeHeat134Fixed12_formula
    · exact nativeHeat134Fixed13_formula
    · exact nativeHeat134Fixed14_formula
    · exact nativeHeat134Fixed15_formula
    · exact nativeHeat134Fixed16_formula
    · exact nativeHeat134Fixed17_formula
    · exact nativeHeat134Fixed18_formula
    · exact nativeHeat134Fixed19_formula
    · exact nativeHeat134Fixed20_formula

theorem nativeHeatStep_chk_134_Gen :
    nativeHeatPassRootsOk nativeGap135Old nativeHeat134Frames nativeHeat134Coef nativeHeat134Fixed nativeHeat134Base 48 nativeHeat134Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_134_Gen : NativeHeatStepPassNum 134 := by
  refine nativeHeatStepPassNum_of_literals 134 nativeGap135Old nativeHeat134Frames (nativeHeatExpArg nativeGap135Old)
    nativeHeat134Exp nativeHeat134Coef nativeHeat134Fixed nativeHeat134Init nativeHeat134Base nativeHeatStep_hOld_134_Gen
    nativeHeatStep_hFr_134_Gen nativeHeatStep_hArg_134_Gen nativeHeatStep_hExp_134_Gen
    nativeHeatStep_hCoef_134_Gen nativeHeatStep_hFixed_134_Gen
    nativeHeatStep_hInit_134_Gen nativeHeatStep_hBase_134_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_134_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_134_Gen :
    nativeHeatY0Gen 134 = nativeShiftedFrame 1 (min nativeGap135Old.x nativeGap135Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_134_Gen, nativeHeatStep_hInd_134_Gen]

theorem nativeHeatStepFrameNum_134_Gen : NativeHeatStepFrameNum 134 := by
  have h1 := nativeHeatStep_hOld_134_Gen
  have h2 := nativeHeatStep_hInd_134_Gen
  have h3 := nativeHeatStep_hVar_134_Gen
  have h4 := nativeHeatStep_hQm_134_Gen
  have h5 := nativeHeatStep_hQN_134_Gen
  have h6 := nativeHeatStep_hY0_134_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_134_Gen : NativeHeatStepIndivNum 134 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 134 (by norm_num)) = nativeGap135Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_134_Gen]; exact nativeGap135Old_source
  · rw [hc, nativeHeatStep_hInd_134_Gen]; exact nativeGap135Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_134_Gen : nativeHeatY48Gen 134 = nativeHeat134Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_134_Gen, nativeHeatStep_hFr_134_Gen,
    nativeHeatStep_hCoef_134_Gen, nativeHeatStep_hFixed_134_Gen,
    nativeHeatStep_hBase_134_Gen]
  exact nativeHeat134All48

theorem nativeHeatResultGen_134 : nativeHeatResultGen 134 = nativeHeat134Result := by
  rw [← nativeHeat134Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_134_Gen, nativeHeatStep_hY0_134_Gen, nativeHeatStep_hExp_134_Gen,
    nativeHeatStep_hInit_134_Gen, nativeHeatStep_hFixed_134_Gen]

end ASDExplicitGamma.Native

end
