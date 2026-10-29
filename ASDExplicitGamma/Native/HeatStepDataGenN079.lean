module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat079Complete
public import ASDExplicitGamma.Numerics.Native.Gap080Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_079_Gen : nativeHeatOldRowGen 79 = nativeGap080Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_079_Gen : nativeHeatIndividualGen 79 = nativeGap080Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_079_Gen : nativeHeatGenVariance 79 = nativeHeat079Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_079_Gen, nativeHeat079Variance_formula]

theorem nativeHeatStep_hSpec_079_Gen : nativeHeatGenSpectral 79 = nativeHeat079Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_079_Gen, nativeHeat079Variance_formula]

theorem nativeHeatStep_hQm_079_Gen : nativeHeatGenQm 79 = nativeHeat079Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_079_Gen, nativeHeatStep_hSpec_079_Gen,
    nativeHeat079Qm_formula]

theorem nativeHeatStep_hQN_079_Gen : nativeHeatQNGen 79 = nativeHeat079QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_079_Gen, nativeHeat079QN_formula]

theorem nativeHeatStep_hFr_079_Gen : nativeHeatFramesGen 79 = nativeHeat079Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_079_Gen, nativeHeatStep_hInd_079_Gen,
    nativeHeatStep_hVar_079_Gen, nativeHeatStep_hQN_079_Gen, nativeHeat079Frames_formula]

theorem nativeHeatStep_hArg_079_Gen : nativeHeatExpArgGen 79 = nativeHeatExpArg nativeGap080Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_079_Gen]

theorem nativeHeatStep_hExp_079_Gen : nativeHeatExpGen 79 = nativeHeat079Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_079_Gen, nativeHeat079Exp_formula]

theorem nativeHeatStep_hCoef_079_Gen : nativeHeatCoefGen 79 = nativeHeat079Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_079_Gen, nativeHeat079Coef_formula]

theorem nativeHeatStep_hInit_079_Gen : nativeHeatInitGen 79 = nativeHeat079Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_079_Gen, nativeHeatStep_hVar_079_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat079Init00_formula
    · exact nativeHeat079Init01_formula
    · exact nativeHeat079Init02_formula
    · exact nativeHeat079Init03_formula
    · exact nativeHeat079Init04_formula
    · exact nativeHeat079Init05_formula
    · exact nativeHeat079Init06_formula
    · exact nativeHeat079Init07_formula
    · exact nativeHeat079Init08_formula
    · exact nativeHeat079Init09_formula
    · exact nativeHeat079Init10_formula
    · exact nativeHeat079Init11_formula
    · exact nativeHeat079Init12_formula
    · exact nativeHeat079Init13_formula
    · exact nativeHeat079Init14_formula
    · exact nativeHeat079Init15_formula
    · exact nativeHeat079Init16_formula
    · exact nativeHeat079Init17_formula
    · exact nativeHeat079Init18_formula
    · exact nativeHeat079Init19_formula
    · exact nativeHeat079Init20_formula
theorem nativeHeatStep_hBase_079_Gen : nativeHeatBaseGen 79 = nativeHeat079Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_079_Gen, nativeHeatStep_hInit_079_Gen, nativeHeat079Base_formula]

theorem nativeHeatStep_hFixed_079_Gen : nativeHeatFixedGen 79 = nativeHeat079Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_079_Gen, nativeHeatStep_hFr_079_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat079Fixed01_formula
    · exact nativeHeat079Fixed02_formula
    · exact nativeHeat079Fixed03_formula
    · exact nativeHeat079Fixed04_formula
    · exact nativeHeat079Fixed05_formula
    · exact nativeHeat079Fixed06_formula
    · exact nativeHeat079Fixed07_formula
    · exact nativeHeat079Fixed08_formula
    · exact nativeHeat079Fixed09_formula
    · exact nativeHeat079Fixed10_formula
    · exact nativeHeat079Fixed11_formula
    · exact nativeHeat079Fixed12_formula
    · exact nativeHeat079Fixed13_formula
    · exact nativeHeat079Fixed14_formula
    · exact nativeHeat079Fixed15_formula
    · exact nativeHeat079Fixed16_formula
    · exact nativeHeat079Fixed17_formula
    · exact nativeHeat079Fixed18_formula
    · exact nativeHeat079Fixed19_formula
    · exact nativeHeat079Fixed20_formula

theorem nativeHeatStep_chk_079_Gen :
    nativeHeatPassRootsOk nativeGap080Old nativeHeat079Frames nativeHeat079Coef nativeHeat079Fixed nativeHeat079Base 48 nativeHeat079Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_079_Gen : NativeHeatStepPassNum 79 := by
  refine nativeHeatStepPassNum_of_literals 79 nativeGap080Old nativeHeat079Frames (nativeHeatExpArg nativeGap080Old)
    nativeHeat079Exp nativeHeat079Coef nativeHeat079Fixed nativeHeat079Init nativeHeat079Base nativeHeatStep_hOld_079_Gen
    nativeHeatStep_hFr_079_Gen nativeHeatStep_hArg_079_Gen nativeHeatStep_hExp_079_Gen
    nativeHeatStep_hCoef_079_Gen nativeHeatStep_hFixed_079_Gen
    nativeHeatStep_hInit_079_Gen nativeHeatStep_hBase_079_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_079_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_079_Gen :
    nativeHeatY0Gen 79 = nativeShiftedFrame 1 (min nativeGap080Old.x nativeGap080Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_079_Gen, nativeHeatStep_hInd_079_Gen]

theorem nativeHeatStepFrameNum_079_Gen : NativeHeatStepFrameNum 79 := by
  have h1 := nativeHeatStep_hOld_079_Gen
  have h2 := nativeHeatStep_hInd_079_Gen
  have h3 := nativeHeatStep_hVar_079_Gen
  have h4 := nativeHeatStep_hQm_079_Gen
  have h5 := nativeHeatStep_hQN_079_Gen
  have h6 := nativeHeatStep_hY0_079_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_079_Gen : NativeHeatStepIndivNum 79 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 79 (by norm_num)) = nativeGap080Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_079_Gen]; exact nativeGap080Old_source
  · rw [hc, nativeHeatStep_hInd_079_Gen]; exact nativeGap080Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_079_Gen : nativeHeatY48Gen 79 = nativeHeat079Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_079_Gen, nativeHeatStep_hFr_079_Gen,
    nativeHeatStep_hCoef_079_Gen, nativeHeatStep_hFixed_079_Gen,
    nativeHeatStep_hBase_079_Gen]
  exact nativeHeat079All48

theorem nativeHeatResultGen_079 : nativeHeatResultGen 79 = nativeHeat079Result := by
  rw [← nativeHeat079Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_079_Gen, nativeHeatStep_hY0_079_Gen, nativeHeatStep_hExp_079_Gen,
    nativeHeatStep_hInit_079_Gen, nativeHeatStep_hFixed_079_Gen]

end ASDExplicitGamma.Native

end
