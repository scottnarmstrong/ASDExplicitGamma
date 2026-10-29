module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat124Complete
public import ASDExplicitGamma.Numerics.Native.Gap125Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_124_Gen : nativeHeatOldRowGen 124 = nativeGap125Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_124_Gen : nativeHeatIndividualGen 124 = nativeGap125Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_124_Gen : nativeHeatGenVariance 124 = nativeHeat124Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_124_Gen, nativeHeat124Variance_formula]

theorem nativeHeatStep_hSpec_124_Gen : nativeHeatGenSpectral 124 = nativeHeat124Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_124_Gen, nativeHeat124Variance_formula]

theorem nativeHeatStep_hQm_124_Gen : nativeHeatGenQm 124 = nativeHeat124Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_124_Gen, nativeHeatStep_hSpec_124_Gen,
    nativeHeat124Qm_formula]

theorem nativeHeatStep_hQN_124_Gen : nativeHeatQNGen 124 = nativeHeat124QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_124_Gen, nativeHeat124QN_formula]

theorem nativeHeatStep_hFr_124_Gen : nativeHeatFramesGen 124 = nativeHeat124Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_124_Gen, nativeHeatStep_hInd_124_Gen,
    nativeHeatStep_hVar_124_Gen, nativeHeatStep_hQN_124_Gen, nativeHeat124Frames_formula]

theorem nativeHeatStep_hArg_124_Gen : nativeHeatExpArgGen 124 = nativeHeatExpArg nativeGap125Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_124_Gen]

theorem nativeHeatStep_hExp_124_Gen : nativeHeatExpGen 124 = nativeHeat124Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_124_Gen, nativeHeat124Exp_formula]

theorem nativeHeatStep_hCoef_124_Gen : nativeHeatCoefGen 124 = nativeHeat124Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_124_Gen, nativeHeat124Coef_formula]

theorem nativeHeatStep_hInit_124_Gen : nativeHeatInitGen 124 = nativeHeat124Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_124_Gen, nativeHeatStep_hVar_124_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat124Init00_formula
    · exact nativeHeat124Init01_formula
    · exact nativeHeat124Init02_formula
    · exact nativeHeat124Init03_formula
    · exact nativeHeat124Init04_formula
    · exact nativeHeat124Init05_formula
    · exact nativeHeat124Init06_formula
    · exact nativeHeat124Init07_formula
    · exact nativeHeat124Init08_formula
    · exact nativeHeat124Init09_formula
    · exact nativeHeat124Init10_formula
    · exact nativeHeat124Init11_formula
    · exact nativeHeat124Init12_formula
    · exact nativeHeat124Init13_formula
    · exact nativeHeat124Init14_formula
    · exact nativeHeat124Init15_formula
    · exact nativeHeat124Init16_formula
    · exact nativeHeat124Init17_formula
    · exact nativeHeat124Init18_formula
    · exact nativeHeat124Init19_formula
    · exact nativeHeat124Init20_formula
theorem nativeHeatStep_hBase_124_Gen : nativeHeatBaseGen 124 = nativeHeat124Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_124_Gen, nativeHeatStep_hInit_124_Gen, nativeHeat124Base_formula]

theorem nativeHeatStep_hFixed_124_Gen : nativeHeatFixedGen 124 = nativeHeat124Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_124_Gen, nativeHeatStep_hFr_124_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat124Fixed01_formula
    · exact nativeHeat124Fixed02_formula
    · exact nativeHeat124Fixed03_formula
    · exact nativeHeat124Fixed04_formula
    · exact nativeHeat124Fixed05_formula
    · exact nativeHeat124Fixed06_formula
    · exact nativeHeat124Fixed07_formula
    · exact nativeHeat124Fixed08_formula
    · exact nativeHeat124Fixed09_formula
    · exact nativeHeat124Fixed10_formula
    · exact nativeHeat124Fixed11_formula
    · exact nativeHeat124Fixed12_formula
    · exact nativeHeat124Fixed13_formula
    · exact nativeHeat124Fixed14_formula
    · exact nativeHeat124Fixed15_formula
    · exact nativeHeat124Fixed16_formula
    · exact nativeHeat124Fixed17_formula
    · exact nativeHeat124Fixed18_formula
    · exact nativeHeat124Fixed19_formula
    · exact nativeHeat124Fixed20_formula

theorem nativeHeatStep_chk_124_Gen :
    nativeHeatPassRootsOk nativeGap125Old nativeHeat124Frames nativeHeat124Coef nativeHeat124Fixed nativeHeat124Base 48 nativeHeat124Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_124_Gen : NativeHeatStepPassNum 124 := by
  refine nativeHeatStepPassNum_of_literals 124 nativeGap125Old nativeHeat124Frames (nativeHeatExpArg nativeGap125Old)
    nativeHeat124Exp nativeHeat124Coef nativeHeat124Fixed nativeHeat124Init nativeHeat124Base nativeHeatStep_hOld_124_Gen
    nativeHeatStep_hFr_124_Gen nativeHeatStep_hArg_124_Gen nativeHeatStep_hExp_124_Gen
    nativeHeatStep_hCoef_124_Gen nativeHeatStep_hFixed_124_Gen
    nativeHeatStep_hInit_124_Gen nativeHeatStep_hBase_124_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_124_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_124_Gen :
    nativeHeatY0Gen 124 = nativeShiftedFrame 1 (min nativeGap125Old.x nativeGap125Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_124_Gen, nativeHeatStep_hInd_124_Gen]

theorem nativeHeatStepFrameNum_124_Gen : NativeHeatStepFrameNum 124 := by
  have h1 := nativeHeatStep_hOld_124_Gen
  have h2 := nativeHeatStep_hInd_124_Gen
  have h3 := nativeHeatStep_hVar_124_Gen
  have h4 := nativeHeatStep_hQm_124_Gen
  have h5 := nativeHeatStep_hQN_124_Gen
  have h6 := nativeHeatStep_hY0_124_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_124_Gen : NativeHeatStepIndivNum 124 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 124 (by norm_num)) = nativeGap125Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_124_Gen]; exact nativeGap125Old_source
  · rw [hc, nativeHeatStep_hInd_124_Gen]; exact nativeGap125Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_124_Gen : nativeHeatY48Gen 124 = nativeHeat124Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_124_Gen, nativeHeatStep_hFr_124_Gen,
    nativeHeatStep_hCoef_124_Gen, nativeHeatStep_hFixed_124_Gen,
    nativeHeatStep_hBase_124_Gen]
  exact nativeHeat124All48

theorem nativeHeatResultGen_124 : nativeHeatResultGen 124 = nativeHeat124Result := by
  rw [← nativeHeat124Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_124_Gen, nativeHeatStep_hY0_124_Gen, nativeHeatStep_hExp_124_Gen,
    nativeHeatStep_hInit_124_Gen, nativeHeatStep_hFixed_124_Gen]

end ASDExplicitGamma.Native

end
