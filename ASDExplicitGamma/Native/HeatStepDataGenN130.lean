module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat130Complete
public import ASDExplicitGamma.Numerics.Native.Gap131Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_130_Gen : nativeHeatOldRowGen 130 = nativeGap131Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_130_Gen : nativeHeatIndividualGen 130 = nativeGap131Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_130_Gen : nativeHeatGenVariance 130 = nativeHeat130Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_130_Gen, nativeHeat130Variance_formula]

theorem nativeHeatStep_hSpec_130_Gen : nativeHeatGenSpectral 130 = nativeHeat130Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_130_Gen, nativeHeat130Variance_formula]

theorem nativeHeatStep_hQm_130_Gen : nativeHeatGenQm 130 = nativeHeat130Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_130_Gen, nativeHeatStep_hSpec_130_Gen,
    nativeHeat130Qm_formula]

theorem nativeHeatStep_hQN_130_Gen : nativeHeatQNGen 130 = nativeHeat130QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_130_Gen, nativeHeat130QN_formula]

theorem nativeHeatStep_hFr_130_Gen : nativeHeatFramesGen 130 = nativeHeat130Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_130_Gen, nativeHeatStep_hInd_130_Gen,
    nativeHeatStep_hVar_130_Gen, nativeHeatStep_hQN_130_Gen, nativeHeat130Frames_formula]

theorem nativeHeatStep_hArg_130_Gen : nativeHeatExpArgGen 130 = nativeHeatExpArg nativeGap131Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_130_Gen]

theorem nativeHeatStep_hExp_130_Gen : nativeHeatExpGen 130 = nativeHeat130Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_130_Gen, nativeHeat130Exp_formula]

theorem nativeHeatStep_hCoef_130_Gen : nativeHeatCoefGen 130 = nativeHeat130Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_130_Gen, nativeHeat130Coef_formula]

theorem nativeHeatStep_hInit_130_Gen : nativeHeatInitGen 130 = nativeHeat130Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_130_Gen, nativeHeatStep_hVar_130_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat130Init00_formula
    · exact nativeHeat130Init01_formula
    · exact nativeHeat130Init02_formula
    · exact nativeHeat130Init03_formula
    · exact nativeHeat130Init04_formula
    · exact nativeHeat130Init05_formula
    · exact nativeHeat130Init06_formula
    · exact nativeHeat130Init07_formula
    · exact nativeHeat130Init08_formula
    · exact nativeHeat130Init09_formula
    · exact nativeHeat130Init10_formula
    · exact nativeHeat130Init11_formula
    · exact nativeHeat130Init12_formula
    · exact nativeHeat130Init13_formula
    · exact nativeHeat130Init14_formula
    · exact nativeHeat130Init15_formula
    · exact nativeHeat130Init16_formula
    · exact nativeHeat130Init17_formula
    · exact nativeHeat130Init18_formula
    · exact nativeHeat130Init19_formula
    · exact nativeHeat130Init20_formula
theorem nativeHeatStep_hBase_130_Gen : nativeHeatBaseGen 130 = nativeHeat130Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_130_Gen, nativeHeatStep_hInit_130_Gen, nativeHeat130Base_formula]

theorem nativeHeatStep_hFixed_130_Gen : nativeHeatFixedGen 130 = nativeHeat130Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_130_Gen, nativeHeatStep_hFr_130_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat130Fixed01_formula
    · exact nativeHeat130Fixed02_formula
    · exact nativeHeat130Fixed03_formula
    · exact nativeHeat130Fixed04_formula
    · exact nativeHeat130Fixed05_formula
    · exact nativeHeat130Fixed06_formula
    · exact nativeHeat130Fixed07_formula
    · exact nativeHeat130Fixed08_formula
    · exact nativeHeat130Fixed09_formula
    · exact nativeHeat130Fixed10_formula
    · exact nativeHeat130Fixed11_formula
    · exact nativeHeat130Fixed12_formula
    · exact nativeHeat130Fixed13_formula
    · exact nativeHeat130Fixed14_formula
    · exact nativeHeat130Fixed15_formula
    · exact nativeHeat130Fixed16_formula
    · exact nativeHeat130Fixed17_formula
    · exact nativeHeat130Fixed18_formula
    · exact nativeHeat130Fixed19_formula
    · exact nativeHeat130Fixed20_formula

theorem nativeHeatStep_chk_130_Gen :
    nativeHeatPassRootsOk nativeGap131Old nativeHeat130Frames nativeHeat130Coef nativeHeat130Fixed nativeHeat130Base 48 nativeHeat130Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_130_Gen : NativeHeatStepPassNum 130 := by
  refine nativeHeatStepPassNum_of_literals 130 nativeGap131Old nativeHeat130Frames (nativeHeatExpArg nativeGap131Old)
    nativeHeat130Exp nativeHeat130Coef nativeHeat130Fixed nativeHeat130Init nativeHeat130Base nativeHeatStep_hOld_130_Gen
    nativeHeatStep_hFr_130_Gen nativeHeatStep_hArg_130_Gen nativeHeatStep_hExp_130_Gen
    nativeHeatStep_hCoef_130_Gen nativeHeatStep_hFixed_130_Gen
    nativeHeatStep_hInit_130_Gen nativeHeatStep_hBase_130_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_130_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_130_Gen :
    nativeHeatY0Gen 130 = nativeShiftedFrame 1 (min nativeGap131Old.x nativeGap131Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_130_Gen, nativeHeatStep_hInd_130_Gen]

theorem nativeHeatStepFrameNum_130_Gen : NativeHeatStepFrameNum 130 := by
  have h1 := nativeHeatStep_hOld_130_Gen
  have h2 := nativeHeatStep_hInd_130_Gen
  have h3 := nativeHeatStep_hVar_130_Gen
  have h4 := nativeHeatStep_hQm_130_Gen
  have h5 := nativeHeatStep_hQN_130_Gen
  have h6 := nativeHeatStep_hY0_130_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_130_Gen : NativeHeatStepIndivNum 130 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 130 (by norm_num)) = nativeGap131Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_130_Gen]; exact nativeGap131Old_source
  · rw [hc, nativeHeatStep_hInd_130_Gen]; exact nativeGap131Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_130_Gen : nativeHeatY48Gen 130 = nativeHeat130Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_130_Gen, nativeHeatStep_hFr_130_Gen,
    nativeHeatStep_hCoef_130_Gen, nativeHeatStep_hFixed_130_Gen,
    nativeHeatStep_hBase_130_Gen]
  exact nativeHeat130All48

theorem nativeHeatResultGen_130 : nativeHeatResultGen 130 = nativeHeat130Result := by
  rw [← nativeHeat130Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_130_Gen, nativeHeatStep_hY0_130_Gen, nativeHeatStep_hExp_130_Gen,
    nativeHeatStep_hInit_130_Gen, nativeHeatStep_hFixed_130_Gen]

end ASDExplicitGamma.Native

end
