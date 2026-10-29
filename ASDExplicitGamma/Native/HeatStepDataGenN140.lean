module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat140Complete
public import ASDExplicitGamma.Numerics.Native.Gap141Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_140_Gen : nativeHeatOldRowGen 140 = nativeGap141Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_140_Gen : nativeHeatIndividualGen 140 = nativeGap141Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_140_Gen : nativeHeatGenVariance 140 = nativeHeat140Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_140_Gen, nativeHeat140Variance_formula]

theorem nativeHeatStep_hSpec_140_Gen : nativeHeatGenSpectral 140 = nativeHeat140Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_140_Gen, nativeHeat140Variance_formula]

theorem nativeHeatStep_hQm_140_Gen : nativeHeatGenQm 140 = nativeHeat140Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_140_Gen, nativeHeatStep_hSpec_140_Gen,
    nativeHeat140Qm_formula]

theorem nativeHeatStep_hQN_140_Gen : nativeHeatQNGen 140 = nativeHeat140QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_140_Gen, nativeHeat140QN_formula]

theorem nativeHeatStep_hFr_140_Gen : nativeHeatFramesGen 140 = nativeHeat140Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_140_Gen, nativeHeatStep_hInd_140_Gen,
    nativeHeatStep_hVar_140_Gen, nativeHeatStep_hQN_140_Gen, nativeHeat140Frames_formula]

theorem nativeHeatStep_hArg_140_Gen : nativeHeatExpArgGen 140 = nativeHeatExpArg nativeGap141Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_140_Gen]

theorem nativeHeatStep_hExp_140_Gen : nativeHeatExpGen 140 = nativeHeat140Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_140_Gen, nativeHeat140Exp_formula]

theorem nativeHeatStep_hCoef_140_Gen : nativeHeatCoefGen 140 = nativeHeat140Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_140_Gen, nativeHeat140Coef_formula]

theorem nativeHeatStep_hInit_140_Gen : nativeHeatInitGen 140 = nativeHeat140Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_140_Gen, nativeHeatStep_hVar_140_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat140Init00_formula
    · exact nativeHeat140Init01_formula
    · exact nativeHeat140Init02_formula
    · exact nativeHeat140Init03_formula
    · exact nativeHeat140Init04_formula
    · exact nativeHeat140Init05_formula
    · exact nativeHeat140Init06_formula
    · exact nativeHeat140Init07_formula
    · exact nativeHeat140Init08_formula
    · exact nativeHeat140Init09_formula
    · exact nativeHeat140Init10_formula
    · exact nativeHeat140Init11_formula
    · exact nativeHeat140Init12_formula
    · exact nativeHeat140Init13_formula
    · exact nativeHeat140Init14_formula
    · exact nativeHeat140Init15_formula
    · exact nativeHeat140Init16_formula
    · exact nativeHeat140Init17_formula
    · exact nativeHeat140Init18_formula
    · exact nativeHeat140Init19_formula
    · exact nativeHeat140Init20_formula
theorem nativeHeatStep_hBase_140_Gen : nativeHeatBaseGen 140 = nativeHeat140Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_140_Gen, nativeHeatStep_hInit_140_Gen, nativeHeat140Base_formula]

theorem nativeHeatStep_hFixed_140_Gen : nativeHeatFixedGen 140 = nativeHeat140Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_140_Gen, nativeHeatStep_hFr_140_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat140Fixed01_formula
    · exact nativeHeat140Fixed02_formula
    · exact nativeHeat140Fixed03_formula
    · exact nativeHeat140Fixed04_formula
    · exact nativeHeat140Fixed05_formula
    · exact nativeHeat140Fixed06_formula
    · exact nativeHeat140Fixed07_formula
    · exact nativeHeat140Fixed08_formula
    · exact nativeHeat140Fixed09_formula
    · exact nativeHeat140Fixed10_formula
    · exact nativeHeat140Fixed11_formula
    · exact nativeHeat140Fixed12_formula
    · exact nativeHeat140Fixed13_formula
    · exact nativeHeat140Fixed14_formula
    · exact nativeHeat140Fixed15_formula
    · exact nativeHeat140Fixed16_formula
    · exact nativeHeat140Fixed17_formula
    · exact nativeHeat140Fixed18_formula
    · exact nativeHeat140Fixed19_formula
    · exact nativeHeat140Fixed20_formula

theorem nativeHeatStep_chk_140_Gen :
    nativeHeatPassRootsOk nativeGap141Old nativeHeat140Frames nativeHeat140Coef nativeHeat140Fixed nativeHeat140Base 48 nativeHeat140Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_140_Gen : NativeHeatStepPassNum 140 := by
  refine nativeHeatStepPassNum_of_literals 140 nativeGap141Old nativeHeat140Frames (nativeHeatExpArg nativeGap141Old)
    nativeHeat140Exp nativeHeat140Coef nativeHeat140Fixed nativeHeat140Init nativeHeat140Base nativeHeatStep_hOld_140_Gen
    nativeHeatStep_hFr_140_Gen nativeHeatStep_hArg_140_Gen nativeHeatStep_hExp_140_Gen
    nativeHeatStep_hCoef_140_Gen nativeHeatStep_hFixed_140_Gen
    nativeHeatStep_hInit_140_Gen nativeHeatStep_hBase_140_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_140_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_140_Gen :
    nativeHeatY0Gen 140 = nativeShiftedFrame 1 (min nativeGap141Old.x nativeGap141Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_140_Gen, nativeHeatStep_hInd_140_Gen]

theorem nativeHeatStepFrameNum_140_Gen : NativeHeatStepFrameNum 140 := by
  have h1 := nativeHeatStep_hOld_140_Gen
  have h2 := nativeHeatStep_hInd_140_Gen
  have h3 := nativeHeatStep_hVar_140_Gen
  have h4 := nativeHeatStep_hQm_140_Gen
  have h5 := nativeHeatStep_hQN_140_Gen
  have h6 := nativeHeatStep_hY0_140_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_140_Gen : NativeHeatStepIndivNum 140 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 140 (by norm_num)) = nativeGap141Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_140_Gen]; exact nativeGap141Old_source
  · rw [hc, nativeHeatStep_hInd_140_Gen]; exact nativeGap141Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_140_Gen : nativeHeatY48Gen 140 = nativeHeat140Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_140_Gen, nativeHeatStep_hFr_140_Gen,
    nativeHeatStep_hCoef_140_Gen, nativeHeatStep_hFixed_140_Gen,
    nativeHeatStep_hBase_140_Gen]
  exact nativeHeat140All48

theorem nativeHeatResultGen_140 : nativeHeatResultGen 140 = nativeHeat140Result := by
  rw [← nativeHeat140Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_140_Gen, nativeHeatStep_hY0_140_Gen, nativeHeatStep_hExp_140_Gen,
    nativeHeatStep_hInit_140_Gen, nativeHeatStep_hFixed_140_Gen]

end ASDExplicitGamma.Native

end
