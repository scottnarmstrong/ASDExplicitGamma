module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat024Complete
public import ASDExplicitGamma.Numerics.Native.Gap025Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_024_Gen : nativeHeatOldRowGen 24 = nativeGap025Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_024_Gen : nativeHeatIndividualGen 24 = nativeGap025Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_024_Gen : nativeHeatGenVariance 24 = nativeHeat024Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_024_Gen, nativeHeat024Variance_formula]

theorem nativeHeatStep_hSpec_024_Gen : nativeHeatGenSpectral 24 = nativeHeat024Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_024_Gen, nativeHeat024Variance_formula]

theorem nativeHeatStep_hQm_024_Gen : nativeHeatGenQm 24 = nativeHeat024Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_024_Gen, nativeHeatStep_hSpec_024_Gen,
    nativeHeat024Qm_formula]

theorem nativeHeatStep_hQN_024_Gen : nativeHeatQNGen 24 = nativeHeat024QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_024_Gen, nativeHeat024QN_formula]

theorem nativeHeatStep_hFr_024_Gen : nativeHeatFramesGen 24 = nativeHeat024Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_024_Gen, nativeHeatStep_hInd_024_Gen,
    nativeHeatStep_hVar_024_Gen, nativeHeatStep_hQN_024_Gen, nativeHeat024Frames_formula]

theorem nativeHeatStep_hArg_024_Gen : nativeHeatExpArgGen 24 = nativeHeatExpArg nativeGap025Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_024_Gen]

theorem nativeHeatStep_hExp_024_Gen : nativeHeatExpGen 24 = nativeHeat024Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_024_Gen, nativeHeat024Exp_formula]

theorem nativeHeatStep_hCoef_024_Gen : nativeHeatCoefGen 24 = nativeHeat024Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_024_Gen, nativeHeat024Coef_formula]

theorem nativeHeatStep_hInit_024_Gen : nativeHeatInitGen 24 = nativeHeat024Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_024_Gen, nativeHeatStep_hVar_024_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat024Init00_formula
    · exact nativeHeat024Init01_formula
    · exact nativeHeat024Init02_formula
    · exact nativeHeat024Init03_formula
    · exact nativeHeat024Init04_formula
    · exact nativeHeat024Init05_formula
    · exact nativeHeat024Init06_formula
    · exact nativeHeat024Init07_formula
    · exact nativeHeat024Init08_formula
    · exact nativeHeat024Init09_formula
    · exact nativeHeat024Init10_formula
    · exact nativeHeat024Init11_formula
    · exact nativeHeat024Init12_formula
    · exact nativeHeat024Init13_formula
    · exact nativeHeat024Init14_formula
    · exact nativeHeat024Init15_formula
    · exact nativeHeat024Init16_formula
    · exact nativeHeat024Init17_formula
    · exact nativeHeat024Init18_formula
    · exact nativeHeat024Init19_formula
    · exact nativeHeat024Init20_formula
theorem nativeHeatStep_hBase_024_Gen : nativeHeatBaseGen 24 = nativeHeat024Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_024_Gen, nativeHeatStep_hInit_024_Gen, nativeHeat024Base_formula]

theorem nativeHeatStep_hFixed_024_Gen : nativeHeatFixedGen 24 = nativeHeat024Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_024_Gen, nativeHeatStep_hFr_024_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat024Fixed01_formula
    · exact nativeHeat024Fixed02_formula
    · exact nativeHeat024Fixed03_formula
    · exact nativeHeat024Fixed04_formula
    · exact nativeHeat024Fixed05_formula
    · exact nativeHeat024Fixed06_formula
    · exact nativeHeat024Fixed07_formula
    · exact nativeHeat024Fixed08_formula
    · exact nativeHeat024Fixed09_formula
    · exact nativeHeat024Fixed10_formula
    · exact nativeHeat024Fixed11_formula
    · exact nativeHeat024Fixed12_formula
    · exact nativeHeat024Fixed13_formula
    · exact nativeHeat024Fixed14_formula
    · exact nativeHeat024Fixed15_formula
    · exact nativeHeat024Fixed16_formula
    · exact nativeHeat024Fixed17_formula
    · exact nativeHeat024Fixed18_formula
    · exact nativeHeat024Fixed19_formula
    · exact nativeHeat024Fixed20_formula

theorem nativeHeatStep_chk_024_Gen :
    nativeHeatPassRootsOk nativeGap025Old nativeHeat024Frames nativeHeat024Coef nativeHeat024Fixed nativeHeat024Base 48 nativeHeat024Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_024_Gen : NativeHeatStepPassNum 24 := by
  refine nativeHeatStepPassNum_of_literals 24 nativeGap025Old nativeHeat024Frames (nativeHeatExpArg nativeGap025Old)
    nativeHeat024Exp nativeHeat024Coef nativeHeat024Fixed nativeHeat024Init nativeHeat024Base nativeHeatStep_hOld_024_Gen
    nativeHeatStep_hFr_024_Gen nativeHeatStep_hArg_024_Gen nativeHeatStep_hExp_024_Gen
    nativeHeatStep_hCoef_024_Gen nativeHeatStep_hFixed_024_Gen
    nativeHeatStep_hInit_024_Gen nativeHeatStep_hBase_024_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_024_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_024_Gen :
    nativeHeatY0Gen 24 = nativeShiftedFrame 1 (min nativeGap025Old.x nativeGap025Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_024_Gen, nativeHeatStep_hInd_024_Gen]

theorem nativeHeatStepFrameNum_024_Gen : NativeHeatStepFrameNum 24 := by
  have h1 := nativeHeatStep_hOld_024_Gen
  have h2 := nativeHeatStep_hInd_024_Gen
  have h3 := nativeHeatStep_hVar_024_Gen
  have h4 := nativeHeatStep_hQm_024_Gen
  have h5 := nativeHeatStep_hQN_024_Gen
  have h6 := nativeHeatStep_hY0_024_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_024_Gen : NativeHeatStepIndivNum 24 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 24 (by norm_num)) = nativeGap025Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_024_Gen]; exact nativeGap025Old_source
  · rw [hc, nativeHeatStep_hInd_024_Gen]; exact nativeGap025Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_024_Gen : nativeHeatY48Gen 24 = nativeHeat024Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_024_Gen, nativeHeatStep_hFr_024_Gen,
    nativeHeatStep_hCoef_024_Gen, nativeHeatStep_hFixed_024_Gen,
    nativeHeatStep_hBase_024_Gen]
  exact nativeHeat024All48

theorem nativeHeatResultGen_024 : nativeHeatResultGen 24 = nativeHeat024Result := by
  rw [← nativeHeat024Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_024_Gen, nativeHeatStep_hY0_024_Gen, nativeHeatStep_hExp_024_Gen,
    nativeHeatStep_hInit_024_Gen, nativeHeatStep_hFixed_024_Gen]

end ASDExplicitGamma.Native

end
