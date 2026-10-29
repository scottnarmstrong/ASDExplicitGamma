module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat053Complete
public import ASDExplicitGamma.Numerics.Native.Gap054Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_053_Gen : nativeHeatOldRowGen 53 = nativeGap054Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_053_Gen : nativeHeatIndividualGen 53 = nativeGap054Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_053_Gen : nativeHeatGenVariance 53 = nativeHeat053Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_053_Gen, nativeHeat053Variance_formula]

theorem nativeHeatStep_hSpec_053_Gen : nativeHeatGenSpectral 53 = nativeHeat053Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_053_Gen, nativeHeat053Variance_formula]

theorem nativeHeatStep_hQm_053_Gen : nativeHeatGenQm 53 = nativeHeat053Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_053_Gen, nativeHeatStep_hSpec_053_Gen,
    nativeHeat053Qm_formula]

theorem nativeHeatStep_hQN_053_Gen : nativeHeatQNGen 53 = nativeHeat053QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_053_Gen, nativeHeat053QN_formula]

theorem nativeHeatStep_hFr_053_Gen : nativeHeatFramesGen 53 = nativeHeat053Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_053_Gen, nativeHeatStep_hInd_053_Gen,
    nativeHeatStep_hVar_053_Gen, nativeHeatStep_hQN_053_Gen, nativeHeat053Frames_formula]

theorem nativeHeatStep_hArg_053_Gen : nativeHeatExpArgGen 53 = nativeHeatExpArg nativeGap054Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_053_Gen]

theorem nativeHeatStep_hExp_053_Gen : nativeHeatExpGen 53 = nativeHeat053Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_053_Gen, nativeHeat053Exp_formula]

theorem nativeHeatStep_hCoef_053_Gen : nativeHeatCoefGen 53 = nativeHeat053Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_053_Gen, nativeHeat053Coef_formula]

theorem nativeHeatStep_hInit_053_Gen : nativeHeatInitGen 53 = nativeHeat053Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_053_Gen, nativeHeatStep_hVar_053_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat053Init00_formula
    · exact nativeHeat053Init01_formula
    · exact nativeHeat053Init02_formula
    · exact nativeHeat053Init03_formula
    · exact nativeHeat053Init04_formula
    · exact nativeHeat053Init05_formula
    · exact nativeHeat053Init06_formula
    · exact nativeHeat053Init07_formula
    · exact nativeHeat053Init08_formula
    · exact nativeHeat053Init09_formula
    · exact nativeHeat053Init10_formula
    · exact nativeHeat053Init11_formula
    · exact nativeHeat053Init12_formula
    · exact nativeHeat053Init13_formula
    · exact nativeHeat053Init14_formula
    · exact nativeHeat053Init15_formula
    · exact nativeHeat053Init16_formula
    · exact nativeHeat053Init17_formula
    · exact nativeHeat053Init18_formula
    · exact nativeHeat053Init19_formula
    · exact nativeHeat053Init20_formula
theorem nativeHeatStep_hBase_053_Gen : nativeHeatBaseGen 53 = nativeHeat053Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_053_Gen, nativeHeatStep_hInit_053_Gen, nativeHeat053Base_formula]

theorem nativeHeatStep_hFixed_053_Gen : nativeHeatFixedGen 53 = nativeHeat053Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_053_Gen, nativeHeatStep_hFr_053_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat053Fixed01_formula
    · exact nativeHeat053Fixed02_formula
    · exact nativeHeat053Fixed03_formula
    · exact nativeHeat053Fixed04_formula
    · exact nativeHeat053Fixed05_formula
    · exact nativeHeat053Fixed06_formula
    · exact nativeHeat053Fixed07_formula
    · exact nativeHeat053Fixed08_formula
    · exact nativeHeat053Fixed09_formula
    · exact nativeHeat053Fixed10_formula
    · exact nativeHeat053Fixed11_formula
    · exact nativeHeat053Fixed12_formula
    · exact nativeHeat053Fixed13_formula
    · exact nativeHeat053Fixed14_formula
    · exact nativeHeat053Fixed15_formula
    · exact nativeHeat053Fixed16_formula
    · exact nativeHeat053Fixed17_formula
    · exact nativeHeat053Fixed18_formula
    · exact nativeHeat053Fixed19_formula
    · exact nativeHeat053Fixed20_formula

theorem nativeHeatStep_chk_053_Gen :
    nativeHeatPassRootsOk nativeGap054Old nativeHeat053Frames nativeHeat053Coef nativeHeat053Fixed nativeHeat053Base 48 nativeHeat053Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_053_Gen : NativeHeatStepPassNum 53 := by
  refine nativeHeatStepPassNum_of_literals 53 nativeGap054Old nativeHeat053Frames (nativeHeatExpArg nativeGap054Old)
    nativeHeat053Exp nativeHeat053Coef nativeHeat053Fixed nativeHeat053Init nativeHeat053Base nativeHeatStep_hOld_053_Gen
    nativeHeatStep_hFr_053_Gen nativeHeatStep_hArg_053_Gen nativeHeatStep_hExp_053_Gen
    nativeHeatStep_hCoef_053_Gen nativeHeatStep_hFixed_053_Gen
    nativeHeatStep_hInit_053_Gen nativeHeatStep_hBase_053_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_053_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_053_Gen :
    nativeHeatY0Gen 53 = nativeShiftedFrame 1 (min nativeGap054Old.x nativeGap054Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_053_Gen, nativeHeatStep_hInd_053_Gen]

theorem nativeHeatStepFrameNum_053_Gen : NativeHeatStepFrameNum 53 := by
  have h1 := nativeHeatStep_hOld_053_Gen
  have h2 := nativeHeatStep_hInd_053_Gen
  have h3 := nativeHeatStep_hVar_053_Gen
  have h4 := nativeHeatStep_hQm_053_Gen
  have h5 := nativeHeatStep_hQN_053_Gen
  have h6 := nativeHeatStep_hY0_053_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_053_Gen : NativeHeatStepIndivNum 53 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 53 (by norm_num)) = nativeGap054Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_053_Gen]; exact nativeGap054Old_source
  · rw [hc, nativeHeatStep_hInd_053_Gen]; exact nativeGap054Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_053_Gen : nativeHeatY48Gen 53 = nativeHeat053Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_053_Gen, nativeHeatStep_hFr_053_Gen,
    nativeHeatStep_hCoef_053_Gen, nativeHeatStep_hFixed_053_Gen,
    nativeHeatStep_hBase_053_Gen]
  exact nativeHeat053All48

theorem nativeHeatResultGen_053 : nativeHeatResultGen 53 = nativeHeat053Result := by
  rw [← nativeHeat053Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_053_Gen, nativeHeatStep_hY0_053_Gen, nativeHeatStep_hExp_053_Gen,
    nativeHeatStep_hInit_053_Gen, nativeHeatStep_hFixed_053_Gen]

end ASDExplicitGamma.Native

end
