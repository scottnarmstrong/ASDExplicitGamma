module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat071Complete
public import ASDExplicitGamma.Numerics.Native.Gap072Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_071_Gen : nativeHeatOldRowGen 71 = nativeGap072Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_071_Gen : nativeHeatIndividualGen 71 = nativeGap072Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_071_Gen : nativeHeatGenVariance 71 = nativeHeat071Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_071_Gen, nativeHeat071Variance_formula]

theorem nativeHeatStep_hSpec_071_Gen : nativeHeatGenSpectral 71 = nativeHeat071Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_071_Gen, nativeHeat071Variance_formula]

theorem nativeHeatStep_hQm_071_Gen : nativeHeatGenQm 71 = nativeHeat071Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_071_Gen, nativeHeatStep_hSpec_071_Gen,
    nativeHeat071Qm_formula]

theorem nativeHeatStep_hQN_071_Gen : nativeHeatQNGen 71 = nativeHeat071QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_071_Gen, nativeHeat071QN_formula]

theorem nativeHeatStep_hFr_071_Gen : nativeHeatFramesGen 71 = nativeHeat071Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_071_Gen, nativeHeatStep_hInd_071_Gen,
    nativeHeatStep_hVar_071_Gen, nativeHeatStep_hQN_071_Gen, nativeHeat071Frames_formula]

theorem nativeHeatStep_hArg_071_Gen : nativeHeatExpArgGen 71 = nativeHeatExpArg nativeGap072Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_071_Gen]

theorem nativeHeatStep_hExp_071_Gen : nativeHeatExpGen 71 = nativeHeat071Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_071_Gen, nativeHeat071Exp_formula]

theorem nativeHeatStep_hCoef_071_Gen : nativeHeatCoefGen 71 = nativeHeat071Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_071_Gen, nativeHeat071Coef_formula]

theorem nativeHeatStep_hInit_071_Gen : nativeHeatInitGen 71 = nativeHeat071Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_071_Gen, nativeHeatStep_hVar_071_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat071Init00_formula
    · exact nativeHeat071Init01_formula
    · exact nativeHeat071Init02_formula
    · exact nativeHeat071Init03_formula
    · exact nativeHeat071Init04_formula
    · exact nativeHeat071Init05_formula
    · exact nativeHeat071Init06_formula
    · exact nativeHeat071Init07_formula
    · exact nativeHeat071Init08_formula
    · exact nativeHeat071Init09_formula
    · exact nativeHeat071Init10_formula
    · exact nativeHeat071Init11_formula
    · exact nativeHeat071Init12_formula
    · exact nativeHeat071Init13_formula
    · exact nativeHeat071Init14_formula
    · exact nativeHeat071Init15_formula
    · exact nativeHeat071Init16_formula
    · exact nativeHeat071Init17_formula
    · exact nativeHeat071Init18_formula
    · exact nativeHeat071Init19_formula
    · exact nativeHeat071Init20_formula
theorem nativeHeatStep_hBase_071_Gen : nativeHeatBaseGen 71 = nativeHeat071Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_071_Gen, nativeHeatStep_hInit_071_Gen, nativeHeat071Base_formula]

theorem nativeHeatStep_hFixed_071_Gen : nativeHeatFixedGen 71 = nativeHeat071Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_071_Gen, nativeHeatStep_hFr_071_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat071Fixed01_formula
    · exact nativeHeat071Fixed02_formula
    · exact nativeHeat071Fixed03_formula
    · exact nativeHeat071Fixed04_formula
    · exact nativeHeat071Fixed05_formula
    · exact nativeHeat071Fixed06_formula
    · exact nativeHeat071Fixed07_formula
    · exact nativeHeat071Fixed08_formula
    · exact nativeHeat071Fixed09_formula
    · exact nativeHeat071Fixed10_formula
    · exact nativeHeat071Fixed11_formula
    · exact nativeHeat071Fixed12_formula
    · exact nativeHeat071Fixed13_formula
    · exact nativeHeat071Fixed14_formula
    · exact nativeHeat071Fixed15_formula
    · exact nativeHeat071Fixed16_formula
    · exact nativeHeat071Fixed17_formula
    · exact nativeHeat071Fixed18_formula
    · exact nativeHeat071Fixed19_formula
    · exact nativeHeat071Fixed20_formula

theorem nativeHeatStep_chk_071_Gen :
    nativeHeatPassRootsOk nativeGap072Old nativeHeat071Frames nativeHeat071Coef nativeHeat071Fixed nativeHeat071Base 48 nativeHeat071Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_071_Gen : NativeHeatStepPassNum 71 := by
  refine nativeHeatStepPassNum_of_literals 71 nativeGap072Old nativeHeat071Frames (nativeHeatExpArg nativeGap072Old)
    nativeHeat071Exp nativeHeat071Coef nativeHeat071Fixed nativeHeat071Init nativeHeat071Base nativeHeatStep_hOld_071_Gen
    nativeHeatStep_hFr_071_Gen nativeHeatStep_hArg_071_Gen nativeHeatStep_hExp_071_Gen
    nativeHeatStep_hCoef_071_Gen nativeHeatStep_hFixed_071_Gen
    nativeHeatStep_hInit_071_Gen nativeHeatStep_hBase_071_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_071_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_071_Gen :
    nativeHeatY0Gen 71 = nativeShiftedFrame 1 (min nativeGap072Old.x nativeGap072Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_071_Gen, nativeHeatStep_hInd_071_Gen]

theorem nativeHeatStepFrameNum_071_Gen : NativeHeatStepFrameNum 71 := by
  have h1 := nativeHeatStep_hOld_071_Gen
  have h2 := nativeHeatStep_hInd_071_Gen
  have h3 := nativeHeatStep_hVar_071_Gen
  have h4 := nativeHeatStep_hQm_071_Gen
  have h5 := nativeHeatStep_hQN_071_Gen
  have h6 := nativeHeatStep_hY0_071_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_071_Gen : NativeHeatStepIndivNum 71 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 71 (by norm_num)) = nativeGap072Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_071_Gen]; exact nativeGap072Old_source
  · rw [hc, nativeHeatStep_hInd_071_Gen]; exact nativeGap072Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_071_Gen : nativeHeatY48Gen 71 = nativeHeat071Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_071_Gen, nativeHeatStep_hFr_071_Gen,
    nativeHeatStep_hCoef_071_Gen, nativeHeatStep_hFixed_071_Gen,
    nativeHeatStep_hBase_071_Gen]
  exact nativeHeat071All48

theorem nativeHeatResultGen_071 : nativeHeatResultGen 71 = nativeHeat071Result := by
  rw [← nativeHeat071Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_071_Gen, nativeHeatStep_hY0_071_Gen, nativeHeatStep_hExp_071_Gen,
    nativeHeatStep_hInit_071_Gen, nativeHeatStep_hFixed_071_Gen]

end ASDExplicitGamma.Native

end
