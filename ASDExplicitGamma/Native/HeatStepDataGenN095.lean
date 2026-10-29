module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat095Complete
public import ASDExplicitGamma.Numerics.Native.Gap096Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_095_Gen : nativeHeatOldRowGen 95 = nativeGap096Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_095_Gen : nativeHeatIndividualGen 95 = nativeGap096Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_095_Gen : nativeHeatGenVariance 95 = nativeHeat095Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_095_Gen, nativeHeat095Variance_formula]

theorem nativeHeatStep_hSpec_095_Gen : nativeHeatGenSpectral 95 = nativeHeat095Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_095_Gen, nativeHeat095Variance_formula]

theorem nativeHeatStep_hQm_095_Gen : nativeHeatGenQm 95 = nativeHeat095Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_095_Gen, nativeHeatStep_hSpec_095_Gen,
    nativeHeat095Qm_formula]

theorem nativeHeatStep_hQN_095_Gen : nativeHeatQNGen 95 = nativeHeat095QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_095_Gen, nativeHeat095QN_formula]

theorem nativeHeatStep_hFr_095_Gen : nativeHeatFramesGen 95 = nativeHeat095Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_095_Gen, nativeHeatStep_hInd_095_Gen,
    nativeHeatStep_hVar_095_Gen, nativeHeatStep_hQN_095_Gen, nativeHeat095Frames_formula]

theorem nativeHeatStep_hArg_095_Gen : nativeHeatExpArgGen 95 = nativeHeatExpArg nativeGap096Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_095_Gen]

theorem nativeHeatStep_hExp_095_Gen : nativeHeatExpGen 95 = nativeHeat095Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_095_Gen, nativeHeat095Exp_formula]

theorem nativeHeatStep_hCoef_095_Gen : nativeHeatCoefGen 95 = nativeHeat095Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_095_Gen, nativeHeat095Coef_formula]

theorem nativeHeatStep_hInit_095_Gen : nativeHeatInitGen 95 = nativeHeat095Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_095_Gen, nativeHeatStep_hVar_095_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat095Init00_formula
    · exact nativeHeat095Init01_formula
    · exact nativeHeat095Init02_formula
    · exact nativeHeat095Init03_formula
    · exact nativeHeat095Init04_formula
    · exact nativeHeat095Init05_formula
    · exact nativeHeat095Init06_formula
    · exact nativeHeat095Init07_formula
    · exact nativeHeat095Init08_formula
    · exact nativeHeat095Init09_formula
    · exact nativeHeat095Init10_formula
    · exact nativeHeat095Init11_formula
    · exact nativeHeat095Init12_formula
    · exact nativeHeat095Init13_formula
    · exact nativeHeat095Init14_formula
    · exact nativeHeat095Init15_formula
    · exact nativeHeat095Init16_formula
    · exact nativeHeat095Init17_formula
    · exact nativeHeat095Init18_formula
    · exact nativeHeat095Init19_formula
    · exact nativeHeat095Init20_formula
theorem nativeHeatStep_hBase_095_Gen : nativeHeatBaseGen 95 = nativeHeat095Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_095_Gen, nativeHeatStep_hInit_095_Gen, nativeHeat095Base_formula]

theorem nativeHeatStep_hFixed_095_Gen : nativeHeatFixedGen 95 = nativeHeat095Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_095_Gen, nativeHeatStep_hFr_095_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat095Fixed01_formula
    · exact nativeHeat095Fixed02_formula
    · exact nativeHeat095Fixed03_formula
    · exact nativeHeat095Fixed04_formula
    · exact nativeHeat095Fixed05_formula
    · exact nativeHeat095Fixed06_formula
    · exact nativeHeat095Fixed07_formula
    · exact nativeHeat095Fixed08_formula
    · exact nativeHeat095Fixed09_formula
    · exact nativeHeat095Fixed10_formula
    · exact nativeHeat095Fixed11_formula
    · exact nativeHeat095Fixed12_formula
    · exact nativeHeat095Fixed13_formula
    · exact nativeHeat095Fixed14_formula
    · exact nativeHeat095Fixed15_formula
    · exact nativeHeat095Fixed16_formula
    · exact nativeHeat095Fixed17_formula
    · exact nativeHeat095Fixed18_formula
    · exact nativeHeat095Fixed19_formula
    · exact nativeHeat095Fixed20_formula

theorem nativeHeatStep_chk_095_Gen :
    nativeHeatPassRootsOk nativeGap096Old nativeHeat095Frames nativeHeat095Coef nativeHeat095Fixed nativeHeat095Base 48 nativeHeat095Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_095_Gen : NativeHeatStepPassNum 95 := by
  refine nativeHeatStepPassNum_of_literals 95 nativeGap096Old nativeHeat095Frames (nativeHeatExpArg nativeGap096Old)
    nativeHeat095Exp nativeHeat095Coef nativeHeat095Fixed nativeHeat095Init nativeHeat095Base nativeHeatStep_hOld_095_Gen
    nativeHeatStep_hFr_095_Gen nativeHeatStep_hArg_095_Gen nativeHeatStep_hExp_095_Gen
    nativeHeatStep_hCoef_095_Gen nativeHeatStep_hFixed_095_Gen
    nativeHeatStep_hInit_095_Gen nativeHeatStep_hBase_095_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_095_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_095_Gen :
    nativeHeatY0Gen 95 = nativeShiftedFrame 1 (min nativeGap096Old.x nativeGap096Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_095_Gen, nativeHeatStep_hInd_095_Gen]

theorem nativeHeatStepFrameNum_095_Gen : NativeHeatStepFrameNum 95 := by
  have h1 := nativeHeatStep_hOld_095_Gen
  have h2 := nativeHeatStep_hInd_095_Gen
  have h3 := nativeHeatStep_hVar_095_Gen
  have h4 := nativeHeatStep_hQm_095_Gen
  have h5 := nativeHeatStep_hQN_095_Gen
  have h6 := nativeHeatStep_hY0_095_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_095_Gen : NativeHeatStepIndivNum 95 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 95 (by norm_num)) = nativeGap096Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_095_Gen]; exact nativeGap096Old_source
  · rw [hc, nativeHeatStep_hInd_095_Gen]; exact nativeGap096Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_095_Gen : nativeHeatY48Gen 95 = nativeHeat095Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_095_Gen, nativeHeatStep_hFr_095_Gen,
    nativeHeatStep_hCoef_095_Gen, nativeHeatStep_hFixed_095_Gen,
    nativeHeatStep_hBase_095_Gen]
  exact nativeHeat095All48

theorem nativeHeatResultGen_095 : nativeHeatResultGen 95 = nativeHeat095Result := by
  rw [← nativeHeat095Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_095_Gen, nativeHeatStep_hY0_095_Gen, nativeHeatStep_hExp_095_Gen,
    nativeHeatStep_hInit_095_Gen, nativeHeatStep_hFixed_095_Gen]

end ASDExplicitGamma.Native

end
