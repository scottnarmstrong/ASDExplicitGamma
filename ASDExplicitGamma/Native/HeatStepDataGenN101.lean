module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat101Complete
public import ASDExplicitGamma.Numerics.Native.Gap102Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_101_Gen : nativeHeatOldRowGen 101 = nativeGap102Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_101_Gen : nativeHeatIndividualGen 101 = nativeGap102Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_101_Gen : nativeHeatGenVariance 101 = nativeHeat101Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_101_Gen, nativeHeat101Variance_formula]

theorem nativeHeatStep_hSpec_101_Gen : nativeHeatGenSpectral 101 = nativeHeat101Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_101_Gen, nativeHeat101Variance_formula]

theorem nativeHeatStep_hQm_101_Gen : nativeHeatGenQm 101 = nativeHeat101Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_101_Gen, nativeHeatStep_hSpec_101_Gen,
    nativeHeat101Qm_formula]

theorem nativeHeatStep_hQN_101_Gen : nativeHeatQNGen 101 = nativeHeat101QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_101_Gen, nativeHeat101QN_formula]

theorem nativeHeatStep_hFr_101_Gen : nativeHeatFramesGen 101 = nativeHeat101Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_101_Gen, nativeHeatStep_hInd_101_Gen,
    nativeHeatStep_hVar_101_Gen, nativeHeatStep_hQN_101_Gen, nativeHeat101Frames_formula]

theorem nativeHeatStep_hArg_101_Gen : nativeHeatExpArgGen 101 = nativeHeatExpArg nativeGap102Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_101_Gen]

theorem nativeHeatStep_hExp_101_Gen : nativeHeatExpGen 101 = nativeHeat101Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_101_Gen, nativeHeat101Exp_formula]

theorem nativeHeatStep_hCoef_101_Gen : nativeHeatCoefGen 101 = nativeHeat101Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_101_Gen, nativeHeat101Coef_formula]

theorem nativeHeatStep_hInit_101_Gen : nativeHeatInitGen 101 = nativeHeat101Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_101_Gen, nativeHeatStep_hVar_101_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat101Init00_formula
    · exact nativeHeat101Init01_formula
    · exact nativeHeat101Init02_formula
    · exact nativeHeat101Init03_formula
    · exact nativeHeat101Init04_formula
    · exact nativeHeat101Init05_formula
    · exact nativeHeat101Init06_formula
    · exact nativeHeat101Init07_formula
    · exact nativeHeat101Init08_formula
    · exact nativeHeat101Init09_formula
    · exact nativeHeat101Init10_formula
    · exact nativeHeat101Init11_formula
    · exact nativeHeat101Init12_formula
    · exact nativeHeat101Init13_formula
    · exact nativeHeat101Init14_formula
    · exact nativeHeat101Init15_formula
    · exact nativeHeat101Init16_formula
    · exact nativeHeat101Init17_formula
    · exact nativeHeat101Init18_formula
    · exact nativeHeat101Init19_formula
    · exact nativeHeat101Init20_formula
theorem nativeHeatStep_hBase_101_Gen : nativeHeatBaseGen 101 = nativeHeat101Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_101_Gen, nativeHeatStep_hInit_101_Gen, nativeHeat101Base_formula]

theorem nativeHeatStep_hFixed_101_Gen : nativeHeatFixedGen 101 = nativeHeat101Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_101_Gen, nativeHeatStep_hFr_101_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat101Fixed01_formula
    · exact nativeHeat101Fixed02_formula
    · exact nativeHeat101Fixed03_formula
    · exact nativeHeat101Fixed04_formula
    · exact nativeHeat101Fixed05_formula
    · exact nativeHeat101Fixed06_formula
    · exact nativeHeat101Fixed07_formula
    · exact nativeHeat101Fixed08_formula
    · exact nativeHeat101Fixed09_formula
    · exact nativeHeat101Fixed10_formula
    · exact nativeHeat101Fixed11_formula
    · exact nativeHeat101Fixed12_formula
    · exact nativeHeat101Fixed13_formula
    · exact nativeHeat101Fixed14_formula
    · exact nativeHeat101Fixed15_formula
    · exact nativeHeat101Fixed16_formula
    · exact nativeHeat101Fixed17_formula
    · exact nativeHeat101Fixed18_formula
    · exact nativeHeat101Fixed19_formula
    · exact nativeHeat101Fixed20_formula

theorem nativeHeatStep_chk_101_Gen :
    nativeHeatPassRootsOk nativeGap102Old nativeHeat101Frames nativeHeat101Coef nativeHeat101Fixed nativeHeat101Base 48 nativeHeat101Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_101_Gen : NativeHeatStepPassNum 101 := by
  refine nativeHeatStepPassNum_of_literals 101 nativeGap102Old nativeHeat101Frames (nativeHeatExpArg nativeGap102Old)
    nativeHeat101Exp nativeHeat101Coef nativeHeat101Fixed nativeHeat101Init nativeHeat101Base nativeHeatStep_hOld_101_Gen
    nativeHeatStep_hFr_101_Gen nativeHeatStep_hArg_101_Gen nativeHeatStep_hExp_101_Gen
    nativeHeatStep_hCoef_101_Gen nativeHeatStep_hFixed_101_Gen
    nativeHeatStep_hInit_101_Gen nativeHeatStep_hBase_101_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_101_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_101_Gen :
    nativeHeatY0Gen 101 = nativeShiftedFrame 1 (min nativeGap102Old.x nativeGap102Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_101_Gen, nativeHeatStep_hInd_101_Gen]

theorem nativeHeatStepFrameNum_101_Gen : NativeHeatStepFrameNum 101 := by
  have h1 := nativeHeatStep_hOld_101_Gen
  have h2 := nativeHeatStep_hInd_101_Gen
  have h3 := nativeHeatStep_hVar_101_Gen
  have h4 := nativeHeatStep_hQm_101_Gen
  have h5 := nativeHeatStep_hQN_101_Gen
  have h6 := nativeHeatStep_hY0_101_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_101_Gen : NativeHeatStepIndivNum 101 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 101 (by norm_num)) = nativeGap102Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_101_Gen]; exact nativeGap102Old_source
  · rw [hc, nativeHeatStep_hInd_101_Gen]; exact nativeGap102Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_101_Gen : nativeHeatY48Gen 101 = nativeHeat101Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_101_Gen, nativeHeatStep_hFr_101_Gen,
    nativeHeatStep_hCoef_101_Gen, nativeHeatStep_hFixed_101_Gen,
    nativeHeatStep_hBase_101_Gen]
  exact nativeHeat101All48

theorem nativeHeatResultGen_101 : nativeHeatResultGen 101 = nativeHeat101Result := by
  rw [← nativeHeat101Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_101_Gen, nativeHeatStep_hY0_101_Gen, nativeHeatStep_hExp_101_Gen,
    nativeHeatStep_hInit_101_Gen, nativeHeatStep_hFixed_101_Gen]

end ASDExplicitGamma.Native

end
