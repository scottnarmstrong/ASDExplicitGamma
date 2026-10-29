module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat084Complete
public import ASDExplicitGamma.Numerics.Native.Gap085Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_084_Gen : nativeHeatOldRowGen 84 = nativeGap085Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_084_Gen : nativeHeatIndividualGen 84 = nativeGap085Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_084_Gen : nativeHeatGenVariance 84 = nativeHeat084Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_084_Gen, nativeHeat084Variance_formula]

theorem nativeHeatStep_hSpec_084_Gen : nativeHeatGenSpectral 84 = nativeHeat084Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_084_Gen, nativeHeat084Variance_formula]

theorem nativeHeatStep_hQm_084_Gen : nativeHeatGenQm 84 = nativeHeat084Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_084_Gen, nativeHeatStep_hSpec_084_Gen,
    nativeHeat084Qm_formula]

theorem nativeHeatStep_hQN_084_Gen : nativeHeatQNGen 84 = nativeHeat084QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_084_Gen, nativeHeat084QN_formula]

theorem nativeHeatStep_hFr_084_Gen : nativeHeatFramesGen 84 = nativeHeat084Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_084_Gen, nativeHeatStep_hInd_084_Gen,
    nativeHeatStep_hVar_084_Gen, nativeHeatStep_hQN_084_Gen, nativeHeat084Frames_formula]

theorem nativeHeatStep_hArg_084_Gen : nativeHeatExpArgGen 84 = nativeHeatExpArg nativeGap085Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_084_Gen]

theorem nativeHeatStep_hExp_084_Gen : nativeHeatExpGen 84 = nativeHeat084Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_084_Gen, nativeHeat084Exp_formula]

theorem nativeHeatStep_hCoef_084_Gen : nativeHeatCoefGen 84 = nativeHeat084Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_084_Gen, nativeHeat084Coef_formula]

theorem nativeHeatStep_hInit_084_Gen : nativeHeatInitGen 84 = nativeHeat084Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_084_Gen, nativeHeatStep_hVar_084_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat084Init00_formula
    · exact nativeHeat084Init01_formula
    · exact nativeHeat084Init02_formula
    · exact nativeHeat084Init03_formula
    · exact nativeHeat084Init04_formula
    · exact nativeHeat084Init05_formula
    · exact nativeHeat084Init06_formula
    · exact nativeHeat084Init07_formula
    · exact nativeHeat084Init08_formula
    · exact nativeHeat084Init09_formula
    · exact nativeHeat084Init10_formula
    · exact nativeHeat084Init11_formula
    · exact nativeHeat084Init12_formula
    · exact nativeHeat084Init13_formula
    · exact nativeHeat084Init14_formula
    · exact nativeHeat084Init15_formula
    · exact nativeHeat084Init16_formula
    · exact nativeHeat084Init17_formula
    · exact nativeHeat084Init18_formula
    · exact nativeHeat084Init19_formula
    · exact nativeHeat084Init20_formula
theorem nativeHeatStep_hBase_084_Gen : nativeHeatBaseGen 84 = nativeHeat084Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_084_Gen, nativeHeatStep_hInit_084_Gen, nativeHeat084Base_formula]

theorem nativeHeatStep_hFixed_084_Gen : nativeHeatFixedGen 84 = nativeHeat084Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_084_Gen, nativeHeatStep_hFr_084_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat084Fixed01_formula
    · exact nativeHeat084Fixed02_formula
    · exact nativeHeat084Fixed03_formula
    · exact nativeHeat084Fixed04_formula
    · exact nativeHeat084Fixed05_formula
    · exact nativeHeat084Fixed06_formula
    · exact nativeHeat084Fixed07_formula
    · exact nativeHeat084Fixed08_formula
    · exact nativeHeat084Fixed09_formula
    · exact nativeHeat084Fixed10_formula
    · exact nativeHeat084Fixed11_formula
    · exact nativeHeat084Fixed12_formula
    · exact nativeHeat084Fixed13_formula
    · exact nativeHeat084Fixed14_formula
    · exact nativeHeat084Fixed15_formula
    · exact nativeHeat084Fixed16_formula
    · exact nativeHeat084Fixed17_formula
    · exact nativeHeat084Fixed18_formula
    · exact nativeHeat084Fixed19_formula
    · exact nativeHeat084Fixed20_formula

theorem nativeHeatStep_chk_084_Gen :
    nativeHeatPassRootsOk nativeGap085Old nativeHeat084Frames nativeHeat084Coef nativeHeat084Fixed nativeHeat084Base 48 nativeHeat084Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_084_Gen : NativeHeatStepPassNum 84 := by
  refine nativeHeatStepPassNum_of_literals 84 nativeGap085Old nativeHeat084Frames (nativeHeatExpArg nativeGap085Old)
    nativeHeat084Exp nativeHeat084Coef nativeHeat084Fixed nativeHeat084Init nativeHeat084Base nativeHeatStep_hOld_084_Gen
    nativeHeatStep_hFr_084_Gen nativeHeatStep_hArg_084_Gen nativeHeatStep_hExp_084_Gen
    nativeHeatStep_hCoef_084_Gen nativeHeatStep_hFixed_084_Gen
    nativeHeatStep_hInit_084_Gen nativeHeatStep_hBase_084_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_084_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_084_Gen :
    nativeHeatY0Gen 84 = nativeShiftedFrame 1 (min nativeGap085Old.x nativeGap085Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_084_Gen, nativeHeatStep_hInd_084_Gen]

theorem nativeHeatStepFrameNum_084_Gen : NativeHeatStepFrameNum 84 := by
  have h1 := nativeHeatStep_hOld_084_Gen
  have h2 := nativeHeatStep_hInd_084_Gen
  have h3 := nativeHeatStep_hVar_084_Gen
  have h4 := nativeHeatStep_hQm_084_Gen
  have h5 := nativeHeatStep_hQN_084_Gen
  have h6 := nativeHeatStep_hY0_084_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_084_Gen : NativeHeatStepIndivNum 84 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 84 (by norm_num)) = nativeGap085Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_084_Gen]; exact nativeGap085Old_source
  · rw [hc, nativeHeatStep_hInd_084_Gen]; exact nativeGap085Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_084_Gen : nativeHeatY48Gen 84 = nativeHeat084Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_084_Gen, nativeHeatStep_hFr_084_Gen,
    nativeHeatStep_hCoef_084_Gen, nativeHeatStep_hFixed_084_Gen,
    nativeHeatStep_hBase_084_Gen]
  exact nativeHeat084All48

theorem nativeHeatResultGen_084 : nativeHeatResultGen 84 = nativeHeat084Result := by
  rw [← nativeHeat084Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_084_Gen, nativeHeatStep_hY0_084_Gen, nativeHeatStep_hExp_084_Gen,
    nativeHeatStep_hInit_084_Gen, nativeHeatStep_hFixed_084_Gen]

end ASDExplicitGamma.Native

end
