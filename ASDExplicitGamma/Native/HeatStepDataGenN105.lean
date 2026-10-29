module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat105Complete
public import ASDExplicitGamma.Numerics.Native.Gap106Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_105_Gen : nativeHeatOldRowGen 105 = nativeGap106Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_105_Gen : nativeHeatIndividualGen 105 = nativeGap106Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_105_Gen : nativeHeatGenVariance 105 = nativeHeat105Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_105_Gen, nativeHeat105Variance_formula]

theorem nativeHeatStep_hSpec_105_Gen : nativeHeatGenSpectral 105 = nativeHeat105Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_105_Gen, nativeHeat105Variance_formula]

theorem nativeHeatStep_hQm_105_Gen : nativeHeatGenQm 105 = nativeHeat105Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_105_Gen, nativeHeatStep_hSpec_105_Gen,
    nativeHeat105Qm_formula]

theorem nativeHeatStep_hQN_105_Gen : nativeHeatQNGen 105 = nativeHeat105QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_105_Gen, nativeHeat105QN_formula]

theorem nativeHeatStep_hFr_105_Gen : nativeHeatFramesGen 105 = nativeHeat105Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_105_Gen, nativeHeatStep_hInd_105_Gen,
    nativeHeatStep_hVar_105_Gen, nativeHeatStep_hQN_105_Gen, nativeHeat105Frames_formula]

theorem nativeHeatStep_hArg_105_Gen : nativeHeatExpArgGen 105 = nativeHeatExpArg nativeGap106Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_105_Gen]

theorem nativeHeatStep_hExp_105_Gen : nativeHeatExpGen 105 = nativeHeat105Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_105_Gen, nativeHeat105Exp_formula]

theorem nativeHeatStep_hCoef_105_Gen : nativeHeatCoefGen 105 = nativeHeat105Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_105_Gen, nativeHeat105Coef_formula]

theorem nativeHeatStep_hInit_105_Gen : nativeHeatInitGen 105 = nativeHeat105Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_105_Gen, nativeHeatStep_hVar_105_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat105Init00_formula
    · exact nativeHeat105Init01_formula
    · exact nativeHeat105Init02_formula
    · exact nativeHeat105Init03_formula
    · exact nativeHeat105Init04_formula
    · exact nativeHeat105Init05_formula
    · exact nativeHeat105Init06_formula
    · exact nativeHeat105Init07_formula
    · exact nativeHeat105Init08_formula
    · exact nativeHeat105Init09_formula
    · exact nativeHeat105Init10_formula
    · exact nativeHeat105Init11_formula
    · exact nativeHeat105Init12_formula
    · exact nativeHeat105Init13_formula
    · exact nativeHeat105Init14_formula
    · exact nativeHeat105Init15_formula
    · exact nativeHeat105Init16_formula
    · exact nativeHeat105Init17_formula
    · exact nativeHeat105Init18_formula
    · exact nativeHeat105Init19_formula
    · exact nativeHeat105Init20_formula
theorem nativeHeatStep_hBase_105_Gen : nativeHeatBaseGen 105 = nativeHeat105Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_105_Gen, nativeHeatStep_hInit_105_Gen, nativeHeat105Base_formula]

theorem nativeHeatStep_hFixed_105_Gen : nativeHeatFixedGen 105 = nativeHeat105Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_105_Gen, nativeHeatStep_hFr_105_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat105Fixed01_formula
    · exact nativeHeat105Fixed02_formula
    · exact nativeHeat105Fixed03_formula
    · exact nativeHeat105Fixed04_formula
    · exact nativeHeat105Fixed05_formula
    · exact nativeHeat105Fixed06_formula
    · exact nativeHeat105Fixed07_formula
    · exact nativeHeat105Fixed08_formula
    · exact nativeHeat105Fixed09_formula
    · exact nativeHeat105Fixed10_formula
    · exact nativeHeat105Fixed11_formula
    · exact nativeHeat105Fixed12_formula
    · exact nativeHeat105Fixed13_formula
    · exact nativeHeat105Fixed14_formula
    · exact nativeHeat105Fixed15_formula
    · exact nativeHeat105Fixed16_formula
    · exact nativeHeat105Fixed17_formula
    · exact nativeHeat105Fixed18_formula
    · exact nativeHeat105Fixed19_formula
    · exact nativeHeat105Fixed20_formula

theorem nativeHeatStep_chk_105_Gen :
    nativeHeatPassRootsOk nativeGap106Old nativeHeat105Frames nativeHeat105Coef nativeHeat105Fixed nativeHeat105Base 48 nativeHeat105Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_105_Gen : NativeHeatStepPassNum 105 := by
  refine nativeHeatStepPassNum_of_literals 105 nativeGap106Old nativeHeat105Frames (nativeHeatExpArg nativeGap106Old)
    nativeHeat105Exp nativeHeat105Coef nativeHeat105Fixed nativeHeat105Init nativeHeat105Base nativeHeatStep_hOld_105_Gen
    nativeHeatStep_hFr_105_Gen nativeHeatStep_hArg_105_Gen nativeHeatStep_hExp_105_Gen
    nativeHeatStep_hCoef_105_Gen nativeHeatStep_hFixed_105_Gen
    nativeHeatStep_hInit_105_Gen nativeHeatStep_hBase_105_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_105_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_105_Gen :
    nativeHeatY0Gen 105 = nativeShiftedFrame 1 (min nativeGap106Old.x nativeGap106Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_105_Gen, nativeHeatStep_hInd_105_Gen]

theorem nativeHeatStepFrameNum_105_Gen : NativeHeatStepFrameNum 105 := by
  have h1 := nativeHeatStep_hOld_105_Gen
  have h2 := nativeHeatStep_hInd_105_Gen
  have h3 := nativeHeatStep_hVar_105_Gen
  have h4 := nativeHeatStep_hQm_105_Gen
  have h5 := nativeHeatStep_hQN_105_Gen
  have h6 := nativeHeatStep_hY0_105_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_105_Gen : NativeHeatStepIndivNum 105 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 105 (by norm_num)) = nativeGap106Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_105_Gen]; exact nativeGap106Old_source
  · rw [hc, nativeHeatStep_hInd_105_Gen]; exact nativeGap106Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_105_Gen : nativeHeatY48Gen 105 = nativeHeat105Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_105_Gen, nativeHeatStep_hFr_105_Gen,
    nativeHeatStep_hCoef_105_Gen, nativeHeatStep_hFixed_105_Gen,
    nativeHeatStep_hBase_105_Gen]
  exact nativeHeat105All48

theorem nativeHeatResultGen_105 : nativeHeatResultGen 105 = nativeHeat105Result := by
  rw [← nativeHeat105Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_105_Gen, nativeHeatStep_hY0_105_Gen, nativeHeatStep_hExp_105_Gen,
    nativeHeatStep_hInit_105_Gen, nativeHeatStep_hFixed_105_Gen]

end ASDExplicitGamma.Native

end
