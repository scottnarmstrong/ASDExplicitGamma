module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat146Complete
public import ASDExplicitGamma.Numerics.Native.Gap147Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_146_Gen : nativeHeatOldRowGen 146 = nativeGap147Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_146_Gen : nativeHeatIndividualGen 146 = nativeGap147Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_146_Gen : nativeHeatGenVariance 146 = nativeHeat146Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_146_Gen, nativeHeat146Variance_formula]

theorem nativeHeatStep_hSpec_146_Gen : nativeHeatGenSpectral 146 = nativeHeat146Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_146_Gen, nativeHeat146Variance_formula]

theorem nativeHeatStep_hQm_146_Gen : nativeHeatGenQm 146 = nativeHeat146Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_146_Gen, nativeHeatStep_hSpec_146_Gen,
    nativeHeat146Qm_formula]

theorem nativeHeatStep_hQN_146_Gen : nativeHeatQNGen 146 = nativeHeat146QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_146_Gen, nativeHeat146QN_formula]

theorem nativeHeatStep_hFr_146_Gen : nativeHeatFramesGen 146 = nativeHeat146Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_146_Gen, nativeHeatStep_hInd_146_Gen,
    nativeHeatStep_hVar_146_Gen, nativeHeatStep_hQN_146_Gen, nativeHeat146Frames_formula]

theorem nativeHeatStep_hArg_146_Gen : nativeHeatExpArgGen 146 = nativeHeatExpArg nativeGap147Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_146_Gen]

theorem nativeHeatStep_hExp_146_Gen : nativeHeatExpGen 146 = nativeHeat146Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_146_Gen, nativeHeat146Exp_formula]

theorem nativeHeatStep_hCoef_146_Gen : nativeHeatCoefGen 146 = nativeHeat146Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_146_Gen, nativeHeat146Coef_formula]

theorem nativeHeatStep_hInit_146_Gen : nativeHeatInitGen 146 = nativeHeat146Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_146_Gen, nativeHeatStep_hVar_146_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat146Init00_formula
    · exact nativeHeat146Init01_formula
    · exact nativeHeat146Init02_formula
    · exact nativeHeat146Init03_formula
    · exact nativeHeat146Init04_formula
    · exact nativeHeat146Init05_formula
    · exact nativeHeat146Init06_formula
    · exact nativeHeat146Init07_formula
    · exact nativeHeat146Init08_formula
    · exact nativeHeat146Init09_formula
    · exact nativeHeat146Init10_formula
    · exact nativeHeat146Init11_formula
    · exact nativeHeat146Init12_formula
    · exact nativeHeat146Init13_formula
    · exact nativeHeat146Init14_formula
    · exact nativeHeat146Init15_formula
    · exact nativeHeat146Init16_formula
    · exact nativeHeat146Init17_formula
    · exact nativeHeat146Init18_formula
    · exact nativeHeat146Init19_formula
    · exact nativeHeat146Init20_formula
theorem nativeHeatStep_hBase_146_Gen : nativeHeatBaseGen 146 = nativeHeat146Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_146_Gen, nativeHeatStep_hInit_146_Gen, nativeHeat146Base_formula]

theorem nativeHeatStep_hFixed_146_Gen : nativeHeatFixedGen 146 = nativeHeat146Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_146_Gen, nativeHeatStep_hFr_146_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat146Fixed01_formula
    · exact nativeHeat146Fixed02_formula
    · exact nativeHeat146Fixed03_formula
    · exact nativeHeat146Fixed04_formula
    · exact nativeHeat146Fixed05_formula
    · exact nativeHeat146Fixed06_formula
    · exact nativeHeat146Fixed07_formula
    · exact nativeHeat146Fixed08_formula
    · exact nativeHeat146Fixed09_formula
    · exact nativeHeat146Fixed10_formula
    · exact nativeHeat146Fixed11_formula
    · exact nativeHeat146Fixed12_formula
    · exact nativeHeat146Fixed13_formula
    · exact nativeHeat146Fixed14_formula
    · exact nativeHeat146Fixed15_formula
    · exact nativeHeat146Fixed16_formula
    · exact nativeHeat146Fixed17_formula
    · exact nativeHeat146Fixed18_formula
    · exact nativeHeat146Fixed19_formula
    · exact nativeHeat146Fixed20_formula

theorem nativeHeatStep_chk_146_Gen :
    nativeHeatPassRootsOk nativeGap147Old nativeHeat146Frames nativeHeat146Coef nativeHeat146Fixed nativeHeat146Base 48 nativeHeat146Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_146_Gen : NativeHeatStepPassNum 146 := by
  refine nativeHeatStepPassNum_of_literals 146 nativeGap147Old nativeHeat146Frames (nativeHeatExpArg nativeGap147Old)
    nativeHeat146Exp nativeHeat146Coef nativeHeat146Fixed nativeHeat146Init nativeHeat146Base nativeHeatStep_hOld_146_Gen
    nativeHeatStep_hFr_146_Gen nativeHeatStep_hArg_146_Gen nativeHeatStep_hExp_146_Gen
    nativeHeatStep_hCoef_146_Gen nativeHeatStep_hFixed_146_Gen
    nativeHeatStep_hInit_146_Gen nativeHeatStep_hBase_146_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_146_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_146_Gen :
    nativeHeatY0Gen 146 = nativeShiftedFrame 1 (min nativeGap147Old.x nativeGap147Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_146_Gen, nativeHeatStep_hInd_146_Gen]

theorem nativeHeatStepFrameNum_146_Gen : NativeHeatStepFrameNum 146 := by
  have h1 := nativeHeatStep_hOld_146_Gen
  have h2 := nativeHeatStep_hInd_146_Gen
  have h3 := nativeHeatStep_hVar_146_Gen
  have h4 := nativeHeatStep_hQm_146_Gen
  have h5 := nativeHeatStep_hQN_146_Gen
  have h6 := nativeHeatStep_hY0_146_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_146_Gen : NativeHeatStepIndivNum 146 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 146 (by norm_num)) = nativeGap147Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_146_Gen]; exact nativeGap147Old_source
  · rw [hc, nativeHeatStep_hInd_146_Gen]; exact nativeGap147Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_146_Gen : nativeHeatY48Gen 146 = nativeHeat146Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_146_Gen, nativeHeatStep_hFr_146_Gen,
    nativeHeatStep_hCoef_146_Gen, nativeHeatStep_hFixed_146_Gen,
    nativeHeatStep_hBase_146_Gen]
  exact nativeHeat146All48

theorem nativeHeatResultGen_146 : nativeHeatResultGen 146 = nativeHeat146Result := by
  rw [← nativeHeat146Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_146_Gen, nativeHeatStep_hY0_146_Gen, nativeHeatStep_hExp_146_Gen,
    nativeHeatStep_hInit_146_Gen, nativeHeatStep_hFixed_146_Gen]

end ASDExplicitGamma.Native

end
