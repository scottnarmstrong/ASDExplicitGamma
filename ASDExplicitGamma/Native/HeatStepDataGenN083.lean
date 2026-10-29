module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat083Complete
public import ASDExplicitGamma.Numerics.Native.Gap084Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_083_Gen : nativeHeatOldRowGen 83 = nativeGap084Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_083_Gen : nativeHeatIndividualGen 83 = nativeGap084Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_083_Gen : nativeHeatGenVariance 83 = nativeHeat083Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_083_Gen, nativeHeat083Variance_formula]

theorem nativeHeatStep_hSpec_083_Gen : nativeHeatGenSpectral 83 = nativeHeat083Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_083_Gen, nativeHeat083Variance_formula]

theorem nativeHeatStep_hQm_083_Gen : nativeHeatGenQm 83 = nativeHeat083Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_083_Gen, nativeHeatStep_hSpec_083_Gen,
    nativeHeat083Qm_formula]

theorem nativeHeatStep_hQN_083_Gen : nativeHeatQNGen 83 = nativeHeat083QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_083_Gen, nativeHeat083QN_formula]

theorem nativeHeatStep_hFr_083_Gen : nativeHeatFramesGen 83 = nativeHeat083Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_083_Gen, nativeHeatStep_hInd_083_Gen,
    nativeHeatStep_hVar_083_Gen, nativeHeatStep_hQN_083_Gen, nativeHeat083Frames_formula]

theorem nativeHeatStep_hArg_083_Gen : nativeHeatExpArgGen 83 = nativeHeatExpArg nativeGap084Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_083_Gen]

theorem nativeHeatStep_hExp_083_Gen : nativeHeatExpGen 83 = nativeHeat083Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_083_Gen, nativeHeat083Exp_formula]

theorem nativeHeatStep_hCoef_083_Gen : nativeHeatCoefGen 83 = nativeHeat083Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_083_Gen, nativeHeat083Coef_formula]

theorem nativeHeatStep_hInit_083_Gen : nativeHeatInitGen 83 = nativeHeat083Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_083_Gen, nativeHeatStep_hVar_083_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat083Init00_formula
    · exact nativeHeat083Init01_formula
    · exact nativeHeat083Init02_formula
    · exact nativeHeat083Init03_formula
    · exact nativeHeat083Init04_formula
    · exact nativeHeat083Init05_formula
    · exact nativeHeat083Init06_formula
    · exact nativeHeat083Init07_formula
    · exact nativeHeat083Init08_formula
    · exact nativeHeat083Init09_formula
    · exact nativeHeat083Init10_formula
    · exact nativeHeat083Init11_formula
    · exact nativeHeat083Init12_formula
    · exact nativeHeat083Init13_formula
    · exact nativeHeat083Init14_formula
    · exact nativeHeat083Init15_formula
    · exact nativeHeat083Init16_formula
    · exact nativeHeat083Init17_formula
    · exact nativeHeat083Init18_formula
    · exact nativeHeat083Init19_formula
    · exact nativeHeat083Init20_formula
theorem nativeHeatStep_hBase_083_Gen : nativeHeatBaseGen 83 = nativeHeat083Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_083_Gen, nativeHeatStep_hInit_083_Gen, nativeHeat083Base_formula]

theorem nativeHeatStep_hFixed_083_Gen : nativeHeatFixedGen 83 = nativeHeat083Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_083_Gen, nativeHeatStep_hFr_083_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat083Fixed01_formula
    · exact nativeHeat083Fixed02_formula
    · exact nativeHeat083Fixed03_formula
    · exact nativeHeat083Fixed04_formula
    · exact nativeHeat083Fixed05_formula
    · exact nativeHeat083Fixed06_formula
    · exact nativeHeat083Fixed07_formula
    · exact nativeHeat083Fixed08_formula
    · exact nativeHeat083Fixed09_formula
    · exact nativeHeat083Fixed10_formula
    · exact nativeHeat083Fixed11_formula
    · exact nativeHeat083Fixed12_formula
    · exact nativeHeat083Fixed13_formula
    · exact nativeHeat083Fixed14_formula
    · exact nativeHeat083Fixed15_formula
    · exact nativeHeat083Fixed16_formula
    · exact nativeHeat083Fixed17_formula
    · exact nativeHeat083Fixed18_formula
    · exact nativeHeat083Fixed19_formula
    · exact nativeHeat083Fixed20_formula

theorem nativeHeatStep_chk_083_Gen :
    nativeHeatPassRootsOk nativeGap084Old nativeHeat083Frames nativeHeat083Coef nativeHeat083Fixed nativeHeat083Base 48 nativeHeat083Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_083_Gen : NativeHeatStepPassNum 83 := by
  refine nativeHeatStepPassNum_of_literals 83 nativeGap084Old nativeHeat083Frames (nativeHeatExpArg nativeGap084Old)
    nativeHeat083Exp nativeHeat083Coef nativeHeat083Fixed nativeHeat083Init nativeHeat083Base nativeHeatStep_hOld_083_Gen
    nativeHeatStep_hFr_083_Gen nativeHeatStep_hArg_083_Gen nativeHeatStep_hExp_083_Gen
    nativeHeatStep_hCoef_083_Gen nativeHeatStep_hFixed_083_Gen
    nativeHeatStep_hInit_083_Gen nativeHeatStep_hBase_083_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_083_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_083_Gen :
    nativeHeatY0Gen 83 = nativeShiftedFrame 1 (min nativeGap084Old.x nativeGap084Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_083_Gen, nativeHeatStep_hInd_083_Gen]

theorem nativeHeatStepFrameNum_083_Gen : NativeHeatStepFrameNum 83 := by
  have h1 := nativeHeatStep_hOld_083_Gen
  have h2 := nativeHeatStep_hInd_083_Gen
  have h3 := nativeHeatStep_hVar_083_Gen
  have h4 := nativeHeatStep_hQm_083_Gen
  have h5 := nativeHeatStep_hQN_083_Gen
  have h6 := nativeHeatStep_hY0_083_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_083_Gen : NativeHeatStepIndivNum 83 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 83 (by norm_num)) = nativeGap084Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_083_Gen]; exact nativeGap084Old_source
  · rw [hc, nativeHeatStep_hInd_083_Gen]; exact nativeGap084Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_083_Gen : nativeHeatY48Gen 83 = nativeHeat083Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_083_Gen, nativeHeatStep_hFr_083_Gen,
    nativeHeatStep_hCoef_083_Gen, nativeHeatStep_hFixed_083_Gen,
    nativeHeatStep_hBase_083_Gen]
  exact nativeHeat083All48

theorem nativeHeatResultGen_083 : nativeHeatResultGen 83 = nativeHeat083Result := by
  rw [← nativeHeat083Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_083_Gen, nativeHeatStep_hY0_083_Gen, nativeHeatStep_hExp_083_Gen,
    nativeHeatStep_hInit_083_Gen, nativeHeatStep_hFixed_083_Gen]

end ASDExplicitGamma.Native

end
