module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat107Complete
public import ASDExplicitGamma.Numerics.Native.Gap108Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_107_Gen : nativeHeatOldRowGen 107 = nativeGap108Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_107_Gen : nativeHeatIndividualGen 107 = nativeGap108Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_107_Gen : nativeHeatGenVariance 107 = nativeHeat107Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_107_Gen, nativeHeat107Variance_formula]

theorem nativeHeatStep_hSpec_107_Gen : nativeHeatGenSpectral 107 = nativeHeat107Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_107_Gen, nativeHeat107Variance_formula]

theorem nativeHeatStep_hQm_107_Gen : nativeHeatGenQm 107 = nativeHeat107Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_107_Gen, nativeHeatStep_hSpec_107_Gen,
    nativeHeat107Qm_formula]

theorem nativeHeatStep_hQN_107_Gen : nativeHeatQNGen 107 = nativeHeat107QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_107_Gen, nativeHeat107QN_formula]

theorem nativeHeatStep_hFr_107_Gen : nativeHeatFramesGen 107 = nativeHeat107Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_107_Gen, nativeHeatStep_hInd_107_Gen,
    nativeHeatStep_hVar_107_Gen, nativeHeatStep_hQN_107_Gen, nativeHeat107Frames_formula]

theorem nativeHeatStep_hArg_107_Gen : nativeHeatExpArgGen 107 = nativeHeatExpArg nativeGap108Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_107_Gen]

theorem nativeHeatStep_hExp_107_Gen : nativeHeatExpGen 107 = nativeHeat107Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_107_Gen, nativeHeat107Exp_formula]

theorem nativeHeatStep_hCoef_107_Gen : nativeHeatCoefGen 107 = nativeHeat107Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_107_Gen, nativeHeat107Coef_formula]

theorem nativeHeatStep_hInit_107_Gen : nativeHeatInitGen 107 = nativeHeat107Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_107_Gen, nativeHeatStep_hVar_107_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat107Init00_formula
    · exact nativeHeat107Init01_formula
    · exact nativeHeat107Init02_formula
    · exact nativeHeat107Init03_formula
    · exact nativeHeat107Init04_formula
    · exact nativeHeat107Init05_formula
    · exact nativeHeat107Init06_formula
    · exact nativeHeat107Init07_formula
    · exact nativeHeat107Init08_formula
    · exact nativeHeat107Init09_formula
    · exact nativeHeat107Init10_formula
    · exact nativeHeat107Init11_formula
    · exact nativeHeat107Init12_formula
    · exact nativeHeat107Init13_formula
    · exact nativeHeat107Init14_formula
    · exact nativeHeat107Init15_formula
    · exact nativeHeat107Init16_formula
    · exact nativeHeat107Init17_formula
    · exact nativeHeat107Init18_formula
    · exact nativeHeat107Init19_formula
    · exact nativeHeat107Init20_formula
theorem nativeHeatStep_hBase_107_Gen : nativeHeatBaseGen 107 = nativeHeat107Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_107_Gen, nativeHeatStep_hInit_107_Gen, nativeHeat107Base_formula]

theorem nativeHeatStep_hFixed_107_Gen : nativeHeatFixedGen 107 = nativeHeat107Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_107_Gen, nativeHeatStep_hFr_107_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat107Fixed01_formula
    · exact nativeHeat107Fixed02_formula
    · exact nativeHeat107Fixed03_formula
    · exact nativeHeat107Fixed04_formula
    · exact nativeHeat107Fixed05_formula
    · exact nativeHeat107Fixed06_formula
    · exact nativeHeat107Fixed07_formula
    · exact nativeHeat107Fixed08_formula
    · exact nativeHeat107Fixed09_formula
    · exact nativeHeat107Fixed10_formula
    · exact nativeHeat107Fixed11_formula
    · exact nativeHeat107Fixed12_formula
    · exact nativeHeat107Fixed13_formula
    · exact nativeHeat107Fixed14_formula
    · exact nativeHeat107Fixed15_formula
    · exact nativeHeat107Fixed16_formula
    · exact nativeHeat107Fixed17_formula
    · exact nativeHeat107Fixed18_formula
    · exact nativeHeat107Fixed19_formula
    · exact nativeHeat107Fixed20_formula

theorem nativeHeatStep_chk_107_Gen :
    nativeHeatPassRootsOk nativeGap108Old nativeHeat107Frames nativeHeat107Coef nativeHeat107Fixed nativeHeat107Base 48 nativeHeat107Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_107_Gen : NativeHeatStepPassNum 107 := by
  refine nativeHeatStepPassNum_of_literals 107 nativeGap108Old nativeHeat107Frames (nativeHeatExpArg nativeGap108Old)
    nativeHeat107Exp nativeHeat107Coef nativeHeat107Fixed nativeHeat107Init nativeHeat107Base nativeHeatStep_hOld_107_Gen
    nativeHeatStep_hFr_107_Gen nativeHeatStep_hArg_107_Gen nativeHeatStep_hExp_107_Gen
    nativeHeatStep_hCoef_107_Gen nativeHeatStep_hFixed_107_Gen
    nativeHeatStep_hInit_107_Gen nativeHeatStep_hBase_107_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_107_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_107_Gen :
    nativeHeatY0Gen 107 = nativeShiftedFrame 1 (min nativeGap108Old.x nativeGap108Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_107_Gen, nativeHeatStep_hInd_107_Gen]

theorem nativeHeatStepFrameNum_107_Gen : NativeHeatStepFrameNum 107 := by
  have h1 := nativeHeatStep_hOld_107_Gen
  have h2 := nativeHeatStep_hInd_107_Gen
  have h3 := nativeHeatStep_hVar_107_Gen
  have h4 := nativeHeatStep_hQm_107_Gen
  have h5 := nativeHeatStep_hQN_107_Gen
  have h6 := nativeHeatStep_hY0_107_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_107_Gen : NativeHeatStepIndivNum 107 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 107 (by norm_num)) = nativeGap108Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_107_Gen]; exact nativeGap108Old_source
  · rw [hc, nativeHeatStep_hInd_107_Gen]; exact nativeGap108Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_107_Gen : nativeHeatY48Gen 107 = nativeHeat107Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_107_Gen, nativeHeatStep_hFr_107_Gen,
    nativeHeatStep_hCoef_107_Gen, nativeHeatStep_hFixed_107_Gen,
    nativeHeatStep_hBase_107_Gen]
  exact nativeHeat107All48

theorem nativeHeatResultGen_107 : nativeHeatResultGen 107 = nativeHeat107Result := by
  rw [← nativeHeat107Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_107_Gen, nativeHeatStep_hY0_107_Gen, nativeHeatStep_hExp_107_Gen,
    nativeHeatStep_hInit_107_Gen, nativeHeatStep_hFixed_107_Gen]

end ASDExplicitGamma.Native

end
