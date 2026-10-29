module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat087Complete
public import ASDExplicitGamma.Numerics.Native.Gap088Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_087_Gen : nativeHeatOldRowGen 87 = nativeGap088Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_087_Gen : nativeHeatIndividualGen 87 = nativeGap088Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_087_Gen : nativeHeatGenVariance 87 = nativeHeat087Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_087_Gen, nativeHeat087Variance_formula]

theorem nativeHeatStep_hSpec_087_Gen : nativeHeatGenSpectral 87 = nativeHeat087Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_087_Gen, nativeHeat087Variance_formula]

theorem nativeHeatStep_hQm_087_Gen : nativeHeatGenQm 87 = nativeHeat087Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_087_Gen, nativeHeatStep_hSpec_087_Gen,
    nativeHeat087Qm_formula]

theorem nativeHeatStep_hQN_087_Gen : nativeHeatQNGen 87 = nativeHeat087QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_087_Gen, nativeHeat087QN_formula]

theorem nativeHeatStep_hFr_087_Gen : nativeHeatFramesGen 87 = nativeHeat087Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_087_Gen, nativeHeatStep_hInd_087_Gen,
    nativeHeatStep_hVar_087_Gen, nativeHeatStep_hQN_087_Gen, nativeHeat087Frames_formula]

theorem nativeHeatStep_hArg_087_Gen : nativeHeatExpArgGen 87 = nativeHeatExpArg nativeGap088Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_087_Gen]

theorem nativeHeatStep_hExp_087_Gen : nativeHeatExpGen 87 = nativeHeat087Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_087_Gen, nativeHeat087Exp_formula]

theorem nativeHeatStep_hCoef_087_Gen : nativeHeatCoefGen 87 = nativeHeat087Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_087_Gen, nativeHeat087Coef_formula]

theorem nativeHeatStep_hInit_087_Gen : nativeHeatInitGen 87 = nativeHeat087Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_087_Gen, nativeHeatStep_hVar_087_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat087Init00_formula
    · exact nativeHeat087Init01_formula
    · exact nativeHeat087Init02_formula
    · exact nativeHeat087Init03_formula
    · exact nativeHeat087Init04_formula
    · exact nativeHeat087Init05_formula
    · exact nativeHeat087Init06_formula
    · exact nativeHeat087Init07_formula
    · exact nativeHeat087Init08_formula
    · exact nativeHeat087Init09_formula
    · exact nativeHeat087Init10_formula
    · exact nativeHeat087Init11_formula
    · exact nativeHeat087Init12_formula
    · exact nativeHeat087Init13_formula
    · exact nativeHeat087Init14_formula
    · exact nativeHeat087Init15_formula
    · exact nativeHeat087Init16_formula
    · exact nativeHeat087Init17_formula
    · exact nativeHeat087Init18_formula
    · exact nativeHeat087Init19_formula
    · exact nativeHeat087Init20_formula
theorem nativeHeatStep_hBase_087_Gen : nativeHeatBaseGen 87 = nativeHeat087Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_087_Gen, nativeHeatStep_hInit_087_Gen, nativeHeat087Base_formula]

theorem nativeHeatStep_hFixed_087_Gen : nativeHeatFixedGen 87 = nativeHeat087Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_087_Gen, nativeHeatStep_hFr_087_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat087Fixed01_formula
    · exact nativeHeat087Fixed02_formula
    · exact nativeHeat087Fixed03_formula
    · exact nativeHeat087Fixed04_formula
    · exact nativeHeat087Fixed05_formula
    · exact nativeHeat087Fixed06_formula
    · exact nativeHeat087Fixed07_formula
    · exact nativeHeat087Fixed08_formula
    · exact nativeHeat087Fixed09_formula
    · exact nativeHeat087Fixed10_formula
    · exact nativeHeat087Fixed11_formula
    · exact nativeHeat087Fixed12_formula
    · exact nativeHeat087Fixed13_formula
    · exact nativeHeat087Fixed14_formula
    · exact nativeHeat087Fixed15_formula
    · exact nativeHeat087Fixed16_formula
    · exact nativeHeat087Fixed17_formula
    · exact nativeHeat087Fixed18_formula
    · exact nativeHeat087Fixed19_formula
    · exact nativeHeat087Fixed20_formula

theorem nativeHeatStep_chk_087_Gen :
    nativeHeatPassRootsOk nativeGap088Old nativeHeat087Frames nativeHeat087Coef nativeHeat087Fixed nativeHeat087Base 48 nativeHeat087Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_087_Gen : NativeHeatStepPassNum 87 := by
  refine nativeHeatStepPassNum_of_literals 87 nativeGap088Old nativeHeat087Frames (nativeHeatExpArg nativeGap088Old)
    nativeHeat087Exp nativeHeat087Coef nativeHeat087Fixed nativeHeat087Init nativeHeat087Base nativeHeatStep_hOld_087_Gen
    nativeHeatStep_hFr_087_Gen nativeHeatStep_hArg_087_Gen nativeHeatStep_hExp_087_Gen
    nativeHeatStep_hCoef_087_Gen nativeHeatStep_hFixed_087_Gen
    nativeHeatStep_hInit_087_Gen nativeHeatStep_hBase_087_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_087_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_087_Gen :
    nativeHeatY0Gen 87 = nativeShiftedFrame 1 (min nativeGap088Old.x nativeGap088Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_087_Gen, nativeHeatStep_hInd_087_Gen]

theorem nativeHeatStepFrameNum_087_Gen : NativeHeatStepFrameNum 87 := by
  have h1 := nativeHeatStep_hOld_087_Gen
  have h2 := nativeHeatStep_hInd_087_Gen
  have h3 := nativeHeatStep_hVar_087_Gen
  have h4 := nativeHeatStep_hQm_087_Gen
  have h5 := nativeHeatStep_hQN_087_Gen
  have h6 := nativeHeatStep_hY0_087_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_087_Gen : NativeHeatStepIndivNum 87 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 87 (by norm_num)) = nativeGap088Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_087_Gen]; exact nativeGap088Old_source
  · rw [hc, nativeHeatStep_hInd_087_Gen]; exact nativeGap088Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_087_Gen : nativeHeatY48Gen 87 = nativeHeat087Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_087_Gen, nativeHeatStep_hFr_087_Gen,
    nativeHeatStep_hCoef_087_Gen, nativeHeatStep_hFixed_087_Gen,
    nativeHeatStep_hBase_087_Gen]
  exact nativeHeat087All48

theorem nativeHeatResultGen_087 : nativeHeatResultGen 87 = nativeHeat087Result := by
  rw [← nativeHeat087Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_087_Gen, nativeHeatStep_hY0_087_Gen, nativeHeatStep_hExp_087_Gen,
    nativeHeatStep_hInit_087_Gen, nativeHeatStep_hFixed_087_Gen]

end ASDExplicitGamma.Native

end
