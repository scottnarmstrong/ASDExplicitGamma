module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat026Complete
public import ASDExplicitGamma.Numerics.Native.Gap027Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_026_Gen : nativeHeatOldRowGen 26 = nativeGap027Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_026_Gen : nativeHeatIndividualGen 26 = nativeGap027Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_026_Gen : nativeHeatGenVariance 26 = nativeHeat026Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_026_Gen, nativeHeat026Variance_formula]

theorem nativeHeatStep_hSpec_026_Gen : nativeHeatGenSpectral 26 = nativeHeat026Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_026_Gen, nativeHeat026Variance_formula]

theorem nativeHeatStep_hQm_026_Gen : nativeHeatGenQm 26 = nativeHeat026Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_026_Gen, nativeHeatStep_hSpec_026_Gen,
    nativeHeat026Qm_formula]

theorem nativeHeatStep_hQN_026_Gen : nativeHeatQNGen 26 = nativeHeat026QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_026_Gen, nativeHeat026QN_formula]

theorem nativeHeatStep_hFr_026_Gen : nativeHeatFramesGen 26 = nativeHeat026Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_026_Gen, nativeHeatStep_hInd_026_Gen,
    nativeHeatStep_hVar_026_Gen, nativeHeatStep_hQN_026_Gen, nativeHeat026Frames_formula]

theorem nativeHeatStep_hArg_026_Gen : nativeHeatExpArgGen 26 = nativeHeatExpArg nativeGap027Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_026_Gen]

theorem nativeHeatStep_hExp_026_Gen : nativeHeatExpGen 26 = nativeHeat026Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_026_Gen, nativeHeat026Exp_formula]

theorem nativeHeatStep_hCoef_026_Gen : nativeHeatCoefGen 26 = nativeHeat026Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_026_Gen, nativeHeat026Coef_formula]

theorem nativeHeatStep_hInit_026_Gen : nativeHeatInitGen 26 = nativeHeat026Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_026_Gen, nativeHeatStep_hVar_026_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat026Init00_formula
    · exact nativeHeat026Init01_formula
    · exact nativeHeat026Init02_formula
    · exact nativeHeat026Init03_formula
    · exact nativeHeat026Init04_formula
    · exact nativeHeat026Init05_formula
    · exact nativeHeat026Init06_formula
    · exact nativeHeat026Init07_formula
    · exact nativeHeat026Init08_formula
    · exact nativeHeat026Init09_formula
    · exact nativeHeat026Init10_formula
    · exact nativeHeat026Init11_formula
    · exact nativeHeat026Init12_formula
    · exact nativeHeat026Init13_formula
    · exact nativeHeat026Init14_formula
    · exact nativeHeat026Init15_formula
    · exact nativeHeat026Init16_formula
    · exact nativeHeat026Init17_formula
    · exact nativeHeat026Init18_formula
    · exact nativeHeat026Init19_formula
    · exact nativeHeat026Init20_formula
theorem nativeHeatStep_hBase_026_Gen : nativeHeatBaseGen 26 = nativeHeat026Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_026_Gen, nativeHeatStep_hInit_026_Gen, nativeHeat026Base_formula]

theorem nativeHeatStep_hFixed_026_Gen : nativeHeatFixedGen 26 = nativeHeat026Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_026_Gen, nativeHeatStep_hFr_026_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat026Fixed01_formula
    · exact nativeHeat026Fixed02_formula
    · exact nativeHeat026Fixed03_formula
    · exact nativeHeat026Fixed04_formula
    · exact nativeHeat026Fixed05_formula
    · exact nativeHeat026Fixed06_formula
    · exact nativeHeat026Fixed07_formula
    · exact nativeHeat026Fixed08_formula
    · exact nativeHeat026Fixed09_formula
    · exact nativeHeat026Fixed10_formula
    · exact nativeHeat026Fixed11_formula
    · exact nativeHeat026Fixed12_formula
    · exact nativeHeat026Fixed13_formula
    · exact nativeHeat026Fixed14_formula
    · exact nativeHeat026Fixed15_formula
    · exact nativeHeat026Fixed16_formula
    · exact nativeHeat026Fixed17_formula
    · exact nativeHeat026Fixed18_formula
    · exact nativeHeat026Fixed19_formula
    · exact nativeHeat026Fixed20_formula

theorem nativeHeatStep_chk_026_Gen :
    nativeHeatPassRootsOk nativeGap027Old nativeHeat026Frames nativeHeat026Coef nativeHeat026Fixed nativeHeat026Base 48 nativeHeat026Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_026_Gen : NativeHeatStepPassNum 26 := by
  refine nativeHeatStepPassNum_of_literals 26 nativeGap027Old nativeHeat026Frames (nativeHeatExpArg nativeGap027Old)
    nativeHeat026Exp nativeHeat026Coef nativeHeat026Fixed nativeHeat026Init nativeHeat026Base nativeHeatStep_hOld_026_Gen
    nativeHeatStep_hFr_026_Gen nativeHeatStep_hArg_026_Gen nativeHeatStep_hExp_026_Gen
    nativeHeatStep_hCoef_026_Gen nativeHeatStep_hFixed_026_Gen
    nativeHeatStep_hInit_026_Gen nativeHeatStep_hBase_026_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_026_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_026_Gen :
    nativeHeatY0Gen 26 = nativeShiftedFrame 1 (min nativeGap027Old.x nativeGap027Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_026_Gen, nativeHeatStep_hInd_026_Gen]

theorem nativeHeatStepFrameNum_026_Gen : NativeHeatStepFrameNum 26 := by
  have h1 := nativeHeatStep_hOld_026_Gen
  have h2 := nativeHeatStep_hInd_026_Gen
  have h3 := nativeHeatStep_hVar_026_Gen
  have h4 := nativeHeatStep_hQm_026_Gen
  have h5 := nativeHeatStep_hQN_026_Gen
  have h6 := nativeHeatStep_hY0_026_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_026_Gen : NativeHeatStepIndivNum 26 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 26 (by norm_num)) = nativeGap027Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_026_Gen]; exact nativeGap027Old_source
  · rw [hc, nativeHeatStep_hInd_026_Gen]; exact nativeGap027Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_026_Gen : nativeHeatY48Gen 26 = nativeHeat026Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_026_Gen, nativeHeatStep_hFr_026_Gen,
    nativeHeatStep_hCoef_026_Gen, nativeHeatStep_hFixed_026_Gen,
    nativeHeatStep_hBase_026_Gen]
  exact nativeHeat026All48

theorem nativeHeatResultGen_026 : nativeHeatResultGen 26 = nativeHeat026Result := by
  rw [← nativeHeat026Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_026_Gen, nativeHeatStep_hY0_026_Gen, nativeHeatStep_hExp_026_Gen,
    nativeHeatStep_hInit_026_Gen, nativeHeatStep_hFixed_026_Gen]

end ASDExplicitGamma.Native

end
