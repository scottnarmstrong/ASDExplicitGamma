module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat121Complete
public import ASDExplicitGamma.Numerics.Native.Gap122Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_121_Gen : nativeHeatOldRowGen 121 = nativeGap122Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_121_Gen : nativeHeatIndividualGen 121 = nativeGap122Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_121_Gen : nativeHeatGenVariance 121 = nativeHeat121Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_121_Gen, nativeHeat121Variance_formula]

theorem nativeHeatStep_hSpec_121_Gen : nativeHeatGenSpectral 121 = nativeHeat121Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_121_Gen, nativeHeat121Variance_formula]

theorem nativeHeatStep_hQm_121_Gen : nativeHeatGenQm 121 = nativeHeat121Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_121_Gen, nativeHeatStep_hSpec_121_Gen,
    nativeHeat121Qm_formula]

theorem nativeHeatStep_hQN_121_Gen : nativeHeatQNGen 121 = nativeHeat121QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_121_Gen, nativeHeat121QN_formula]

theorem nativeHeatStep_hFr_121_Gen : nativeHeatFramesGen 121 = nativeHeat121Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_121_Gen, nativeHeatStep_hInd_121_Gen,
    nativeHeatStep_hVar_121_Gen, nativeHeatStep_hQN_121_Gen, nativeHeat121Frames_formula]

theorem nativeHeatStep_hArg_121_Gen : nativeHeatExpArgGen 121 = nativeHeatExpArg nativeGap122Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_121_Gen]

theorem nativeHeatStep_hExp_121_Gen : nativeHeatExpGen 121 = nativeHeat121Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_121_Gen, nativeHeat121Exp_formula]

theorem nativeHeatStep_hCoef_121_Gen : nativeHeatCoefGen 121 = nativeHeat121Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_121_Gen, nativeHeat121Coef_formula]

theorem nativeHeatStep_hInit_121_Gen : nativeHeatInitGen 121 = nativeHeat121Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_121_Gen, nativeHeatStep_hVar_121_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat121Init00_formula
    · exact nativeHeat121Init01_formula
    · exact nativeHeat121Init02_formula
    · exact nativeHeat121Init03_formula
    · exact nativeHeat121Init04_formula
    · exact nativeHeat121Init05_formula
    · exact nativeHeat121Init06_formula
    · exact nativeHeat121Init07_formula
    · exact nativeHeat121Init08_formula
    · exact nativeHeat121Init09_formula
    · exact nativeHeat121Init10_formula
    · exact nativeHeat121Init11_formula
    · exact nativeHeat121Init12_formula
    · exact nativeHeat121Init13_formula
    · exact nativeHeat121Init14_formula
    · exact nativeHeat121Init15_formula
    · exact nativeHeat121Init16_formula
    · exact nativeHeat121Init17_formula
    · exact nativeHeat121Init18_formula
    · exact nativeHeat121Init19_formula
    · exact nativeHeat121Init20_formula
theorem nativeHeatStep_hBase_121_Gen : nativeHeatBaseGen 121 = nativeHeat121Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_121_Gen, nativeHeatStep_hInit_121_Gen, nativeHeat121Base_formula]

theorem nativeHeatStep_hFixed_121_Gen : nativeHeatFixedGen 121 = nativeHeat121Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_121_Gen, nativeHeatStep_hFr_121_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat121Fixed01_formula
    · exact nativeHeat121Fixed02_formula
    · exact nativeHeat121Fixed03_formula
    · exact nativeHeat121Fixed04_formula
    · exact nativeHeat121Fixed05_formula
    · exact nativeHeat121Fixed06_formula
    · exact nativeHeat121Fixed07_formula
    · exact nativeHeat121Fixed08_formula
    · exact nativeHeat121Fixed09_formula
    · exact nativeHeat121Fixed10_formula
    · exact nativeHeat121Fixed11_formula
    · exact nativeHeat121Fixed12_formula
    · exact nativeHeat121Fixed13_formula
    · exact nativeHeat121Fixed14_formula
    · exact nativeHeat121Fixed15_formula
    · exact nativeHeat121Fixed16_formula
    · exact nativeHeat121Fixed17_formula
    · exact nativeHeat121Fixed18_formula
    · exact nativeHeat121Fixed19_formula
    · exact nativeHeat121Fixed20_formula

theorem nativeHeatStep_chk_121_Gen :
    nativeHeatPassRootsOk nativeGap122Old nativeHeat121Frames nativeHeat121Coef nativeHeat121Fixed nativeHeat121Base 48 nativeHeat121Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_121_Gen : NativeHeatStepPassNum 121 := by
  refine nativeHeatStepPassNum_of_literals 121 nativeGap122Old nativeHeat121Frames (nativeHeatExpArg nativeGap122Old)
    nativeHeat121Exp nativeHeat121Coef nativeHeat121Fixed nativeHeat121Init nativeHeat121Base nativeHeatStep_hOld_121_Gen
    nativeHeatStep_hFr_121_Gen nativeHeatStep_hArg_121_Gen nativeHeatStep_hExp_121_Gen
    nativeHeatStep_hCoef_121_Gen nativeHeatStep_hFixed_121_Gen
    nativeHeatStep_hInit_121_Gen nativeHeatStep_hBase_121_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_121_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_121_Gen :
    nativeHeatY0Gen 121 = nativeShiftedFrame 1 (min nativeGap122Old.x nativeGap122Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_121_Gen, nativeHeatStep_hInd_121_Gen]

theorem nativeHeatStepFrameNum_121_Gen : NativeHeatStepFrameNum 121 := by
  have h1 := nativeHeatStep_hOld_121_Gen
  have h2 := nativeHeatStep_hInd_121_Gen
  have h3 := nativeHeatStep_hVar_121_Gen
  have h4 := nativeHeatStep_hQm_121_Gen
  have h5 := nativeHeatStep_hQN_121_Gen
  have h6 := nativeHeatStep_hY0_121_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_121_Gen : NativeHeatStepIndivNum 121 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 121 (by norm_num)) = nativeGap122Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_121_Gen]; exact nativeGap122Old_source
  · rw [hc, nativeHeatStep_hInd_121_Gen]; exact nativeGap122Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_121_Gen : nativeHeatY48Gen 121 = nativeHeat121Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_121_Gen, nativeHeatStep_hFr_121_Gen,
    nativeHeatStep_hCoef_121_Gen, nativeHeatStep_hFixed_121_Gen,
    nativeHeatStep_hBase_121_Gen]
  exact nativeHeat121All48

theorem nativeHeatResultGen_121 : nativeHeatResultGen 121 = nativeHeat121Result := by
  rw [← nativeHeat121Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_121_Gen, nativeHeatStep_hY0_121_Gen, nativeHeatStep_hExp_121_Gen,
    nativeHeatStep_hInit_121_Gen, nativeHeatStep_hFixed_121_Gen]

end ASDExplicitGamma.Native

end
