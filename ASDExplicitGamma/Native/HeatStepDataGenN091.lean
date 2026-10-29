module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat091Complete
public import ASDExplicitGamma.Numerics.Native.Gap092Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_091_Gen : nativeHeatOldRowGen 91 = nativeGap092Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_091_Gen : nativeHeatIndividualGen 91 = nativeGap092Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_091_Gen : nativeHeatGenVariance 91 = nativeHeat091Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_091_Gen, nativeHeat091Variance_formula]

theorem nativeHeatStep_hSpec_091_Gen : nativeHeatGenSpectral 91 = nativeHeat091Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_091_Gen, nativeHeat091Variance_formula]

theorem nativeHeatStep_hQm_091_Gen : nativeHeatGenQm 91 = nativeHeat091Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_091_Gen, nativeHeatStep_hSpec_091_Gen,
    nativeHeat091Qm_formula]

theorem nativeHeatStep_hQN_091_Gen : nativeHeatQNGen 91 = nativeHeat091QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_091_Gen, nativeHeat091QN_formula]

theorem nativeHeatStep_hFr_091_Gen : nativeHeatFramesGen 91 = nativeHeat091Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_091_Gen, nativeHeatStep_hInd_091_Gen,
    nativeHeatStep_hVar_091_Gen, nativeHeatStep_hQN_091_Gen, nativeHeat091Frames_formula]

theorem nativeHeatStep_hArg_091_Gen : nativeHeatExpArgGen 91 = nativeHeatExpArg nativeGap092Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_091_Gen]

theorem nativeHeatStep_hExp_091_Gen : nativeHeatExpGen 91 = nativeHeat091Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_091_Gen, nativeHeat091Exp_formula]

theorem nativeHeatStep_hCoef_091_Gen : nativeHeatCoefGen 91 = nativeHeat091Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_091_Gen, nativeHeat091Coef_formula]

theorem nativeHeatStep_hInit_091_Gen : nativeHeatInitGen 91 = nativeHeat091Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_091_Gen, nativeHeatStep_hVar_091_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat091Init00_formula
    · exact nativeHeat091Init01_formula
    · exact nativeHeat091Init02_formula
    · exact nativeHeat091Init03_formula
    · exact nativeHeat091Init04_formula
    · exact nativeHeat091Init05_formula
    · exact nativeHeat091Init06_formula
    · exact nativeHeat091Init07_formula
    · exact nativeHeat091Init08_formula
    · exact nativeHeat091Init09_formula
    · exact nativeHeat091Init10_formula
    · exact nativeHeat091Init11_formula
    · exact nativeHeat091Init12_formula
    · exact nativeHeat091Init13_formula
    · exact nativeHeat091Init14_formula
    · exact nativeHeat091Init15_formula
    · exact nativeHeat091Init16_formula
    · exact nativeHeat091Init17_formula
    · exact nativeHeat091Init18_formula
    · exact nativeHeat091Init19_formula
    · exact nativeHeat091Init20_formula
theorem nativeHeatStep_hBase_091_Gen : nativeHeatBaseGen 91 = nativeHeat091Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_091_Gen, nativeHeatStep_hInit_091_Gen, nativeHeat091Base_formula]

theorem nativeHeatStep_hFixed_091_Gen : nativeHeatFixedGen 91 = nativeHeat091Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_091_Gen, nativeHeatStep_hFr_091_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat091Fixed01_formula
    · exact nativeHeat091Fixed02_formula
    · exact nativeHeat091Fixed03_formula
    · exact nativeHeat091Fixed04_formula
    · exact nativeHeat091Fixed05_formula
    · exact nativeHeat091Fixed06_formula
    · exact nativeHeat091Fixed07_formula
    · exact nativeHeat091Fixed08_formula
    · exact nativeHeat091Fixed09_formula
    · exact nativeHeat091Fixed10_formula
    · exact nativeHeat091Fixed11_formula
    · exact nativeHeat091Fixed12_formula
    · exact nativeHeat091Fixed13_formula
    · exact nativeHeat091Fixed14_formula
    · exact nativeHeat091Fixed15_formula
    · exact nativeHeat091Fixed16_formula
    · exact nativeHeat091Fixed17_formula
    · exact nativeHeat091Fixed18_formula
    · exact nativeHeat091Fixed19_formula
    · exact nativeHeat091Fixed20_formula

theorem nativeHeatStep_chk_091_Gen :
    nativeHeatPassRootsOk nativeGap092Old nativeHeat091Frames nativeHeat091Coef nativeHeat091Fixed nativeHeat091Base 48 nativeHeat091Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_091_Gen : NativeHeatStepPassNum 91 := by
  refine nativeHeatStepPassNum_of_literals 91 nativeGap092Old nativeHeat091Frames (nativeHeatExpArg nativeGap092Old)
    nativeHeat091Exp nativeHeat091Coef nativeHeat091Fixed nativeHeat091Init nativeHeat091Base nativeHeatStep_hOld_091_Gen
    nativeHeatStep_hFr_091_Gen nativeHeatStep_hArg_091_Gen nativeHeatStep_hExp_091_Gen
    nativeHeatStep_hCoef_091_Gen nativeHeatStep_hFixed_091_Gen
    nativeHeatStep_hInit_091_Gen nativeHeatStep_hBase_091_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_091_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_091_Gen :
    nativeHeatY0Gen 91 = nativeShiftedFrame 1 (min nativeGap092Old.x nativeGap092Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_091_Gen, nativeHeatStep_hInd_091_Gen]

theorem nativeHeatStepFrameNum_091_Gen : NativeHeatStepFrameNum 91 := by
  have h1 := nativeHeatStep_hOld_091_Gen
  have h2 := nativeHeatStep_hInd_091_Gen
  have h3 := nativeHeatStep_hVar_091_Gen
  have h4 := nativeHeatStep_hQm_091_Gen
  have h5 := nativeHeatStep_hQN_091_Gen
  have h6 := nativeHeatStep_hY0_091_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_091_Gen : NativeHeatStepIndivNum 91 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 91 (by norm_num)) = nativeGap092Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_091_Gen]; exact nativeGap092Old_source
  · rw [hc, nativeHeatStep_hInd_091_Gen]; exact nativeGap092Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_091_Gen : nativeHeatY48Gen 91 = nativeHeat091Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_091_Gen, nativeHeatStep_hFr_091_Gen,
    nativeHeatStep_hCoef_091_Gen, nativeHeatStep_hFixed_091_Gen,
    nativeHeatStep_hBase_091_Gen]
  exact nativeHeat091All48

theorem nativeHeatResultGen_091 : nativeHeatResultGen 91 = nativeHeat091Result := by
  rw [← nativeHeat091Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_091_Gen, nativeHeatStep_hY0_091_Gen, nativeHeatStep_hExp_091_Gen,
    nativeHeatStep_hInit_091_Gen, nativeHeatStep_hFixed_091_Gen]

end ASDExplicitGamma.Native

end
