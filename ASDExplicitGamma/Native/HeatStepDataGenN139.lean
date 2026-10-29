module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat139Complete
public import ASDExplicitGamma.Numerics.Native.Gap140Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_139_Gen : nativeHeatOldRowGen 139 = nativeGap140Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_139_Gen : nativeHeatIndividualGen 139 = nativeGap140Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_139_Gen : nativeHeatGenVariance 139 = nativeHeat139Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_139_Gen, nativeHeat139Variance_formula]

theorem nativeHeatStep_hSpec_139_Gen : nativeHeatGenSpectral 139 = nativeHeat139Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_139_Gen, nativeHeat139Variance_formula]

theorem nativeHeatStep_hQm_139_Gen : nativeHeatGenQm 139 = nativeHeat139Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_139_Gen, nativeHeatStep_hSpec_139_Gen,
    nativeHeat139Qm_formula]

theorem nativeHeatStep_hQN_139_Gen : nativeHeatQNGen 139 = nativeHeat139QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_139_Gen, nativeHeat139QN_formula]

theorem nativeHeatStep_hFr_139_Gen : nativeHeatFramesGen 139 = nativeHeat139Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_139_Gen, nativeHeatStep_hInd_139_Gen,
    nativeHeatStep_hVar_139_Gen, nativeHeatStep_hQN_139_Gen, nativeHeat139Frames_formula]

theorem nativeHeatStep_hArg_139_Gen : nativeHeatExpArgGen 139 = nativeHeatExpArg nativeGap140Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_139_Gen]

theorem nativeHeatStep_hExp_139_Gen : nativeHeatExpGen 139 = nativeHeat139Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_139_Gen, nativeHeat139Exp_formula]

theorem nativeHeatStep_hCoef_139_Gen : nativeHeatCoefGen 139 = nativeHeat139Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_139_Gen, nativeHeat139Coef_formula]

theorem nativeHeatStep_hInit_139_Gen : nativeHeatInitGen 139 = nativeHeat139Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_139_Gen, nativeHeatStep_hVar_139_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat139Init00_formula
    · exact nativeHeat139Init01_formula
    · exact nativeHeat139Init02_formula
    · exact nativeHeat139Init03_formula
    · exact nativeHeat139Init04_formula
    · exact nativeHeat139Init05_formula
    · exact nativeHeat139Init06_formula
    · exact nativeHeat139Init07_formula
    · exact nativeHeat139Init08_formula
    · exact nativeHeat139Init09_formula
    · exact nativeHeat139Init10_formula
    · exact nativeHeat139Init11_formula
    · exact nativeHeat139Init12_formula
    · exact nativeHeat139Init13_formula
    · exact nativeHeat139Init14_formula
    · exact nativeHeat139Init15_formula
    · exact nativeHeat139Init16_formula
    · exact nativeHeat139Init17_formula
    · exact nativeHeat139Init18_formula
    · exact nativeHeat139Init19_formula
    · exact nativeHeat139Init20_formula
theorem nativeHeatStep_hBase_139_Gen : nativeHeatBaseGen 139 = nativeHeat139Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_139_Gen, nativeHeatStep_hInit_139_Gen, nativeHeat139Base_formula]

theorem nativeHeatStep_hFixed_139_Gen : nativeHeatFixedGen 139 = nativeHeat139Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_139_Gen, nativeHeatStep_hFr_139_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat139Fixed01_formula
    · exact nativeHeat139Fixed02_formula
    · exact nativeHeat139Fixed03_formula
    · exact nativeHeat139Fixed04_formula
    · exact nativeHeat139Fixed05_formula
    · exact nativeHeat139Fixed06_formula
    · exact nativeHeat139Fixed07_formula
    · exact nativeHeat139Fixed08_formula
    · exact nativeHeat139Fixed09_formula
    · exact nativeHeat139Fixed10_formula
    · exact nativeHeat139Fixed11_formula
    · exact nativeHeat139Fixed12_formula
    · exact nativeHeat139Fixed13_formula
    · exact nativeHeat139Fixed14_formula
    · exact nativeHeat139Fixed15_formula
    · exact nativeHeat139Fixed16_formula
    · exact nativeHeat139Fixed17_formula
    · exact nativeHeat139Fixed18_formula
    · exact nativeHeat139Fixed19_formula
    · exact nativeHeat139Fixed20_formula

theorem nativeHeatStep_chk_139_Gen :
    nativeHeatPassRootsOk nativeGap140Old nativeHeat139Frames nativeHeat139Coef nativeHeat139Fixed nativeHeat139Base 48 nativeHeat139Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_139_Gen : NativeHeatStepPassNum 139 := by
  refine nativeHeatStepPassNum_of_literals 139 nativeGap140Old nativeHeat139Frames (nativeHeatExpArg nativeGap140Old)
    nativeHeat139Exp nativeHeat139Coef nativeHeat139Fixed nativeHeat139Init nativeHeat139Base nativeHeatStep_hOld_139_Gen
    nativeHeatStep_hFr_139_Gen nativeHeatStep_hArg_139_Gen nativeHeatStep_hExp_139_Gen
    nativeHeatStep_hCoef_139_Gen nativeHeatStep_hFixed_139_Gen
    nativeHeatStep_hInit_139_Gen nativeHeatStep_hBase_139_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_139_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_139_Gen :
    nativeHeatY0Gen 139 = nativeShiftedFrame 1 (min nativeGap140Old.x nativeGap140Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_139_Gen, nativeHeatStep_hInd_139_Gen]

theorem nativeHeatStepFrameNum_139_Gen : NativeHeatStepFrameNum 139 := by
  have h1 := nativeHeatStep_hOld_139_Gen
  have h2 := nativeHeatStep_hInd_139_Gen
  have h3 := nativeHeatStep_hVar_139_Gen
  have h4 := nativeHeatStep_hQm_139_Gen
  have h5 := nativeHeatStep_hQN_139_Gen
  have h6 := nativeHeatStep_hY0_139_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_139_Gen : NativeHeatStepIndivNum 139 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 139 (by norm_num)) = nativeGap140Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_139_Gen]; exact nativeGap140Old_source
  · rw [hc, nativeHeatStep_hInd_139_Gen]; exact nativeGap140Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_139_Gen : nativeHeatY48Gen 139 = nativeHeat139Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_139_Gen, nativeHeatStep_hFr_139_Gen,
    nativeHeatStep_hCoef_139_Gen, nativeHeatStep_hFixed_139_Gen,
    nativeHeatStep_hBase_139_Gen]
  exact nativeHeat139All48

theorem nativeHeatResultGen_139 : nativeHeatResultGen 139 = nativeHeat139Result := by
  rw [← nativeHeat139Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_139_Gen, nativeHeatStep_hY0_139_Gen, nativeHeatStep_hExp_139_Gen,
    nativeHeatStep_hInit_139_Gen, nativeHeatStep_hFixed_139_Gen]

end ASDExplicitGamma.Native

end
