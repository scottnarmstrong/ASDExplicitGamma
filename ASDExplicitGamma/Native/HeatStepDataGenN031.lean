module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat031Complete
public import ASDExplicitGamma.Numerics.Native.Gap032Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_031_Gen : nativeHeatOldRowGen 31 = nativeGap032Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_031_Gen : nativeHeatIndividualGen 31 = nativeGap032Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_031_Gen : nativeHeatGenVariance 31 = nativeHeat031Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_031_Gen, nativeHeat031Variance_formula]

theorem nativeHeatStep_hSpec_031_Gen : nativeHeatGenSpectral 31 = nativeHeat031Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_031_Gen, nativeHeat031Variance_formula]

theorem nativeHeatStep_hQm_031_Gen : nativeHeatGenQm 31 = nativeHeat031Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_031_Gen, nativeHeatStep_hSpec_031_Gen,
    nativeHeat031Qm_formula]

theorem nativeHeatStep_hQN_031_Gen : nativeHeatQNGen 31 = nativeHeat031QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_031_Gen, nativeHeat031QN_formula]

theorem nativeHeatStep_hFr_031_Gen : nativeHeatFramesGen 31 = nativeHeat031Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_031_Gen, nativeHeatStep_hInd_031_Gen,
    nativeHeatStep_hVar_031_Gen, nativeHeatStep_hQN_031_Gen, nativeHeat031Frames_formula]

theorem nativeHeatStep_hArg_031_Gen : nativeHeatExpArgGen 31 = nativeHeatExpArg nativeGap032Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_031_Gen]

theorem nativeHeatStep_hExp_031_Gen : nativeHeatExpGen 31 = nativeHeat031Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_031_Gen, nativeHeat031Exp_formula]

theorem nativeHeatStep_hCoef_031_Gen : nativeHeatCoefGen 31 = nativeHeat031Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_031_Gen, nativeHeat031Coef_formula]

theorem nativeHeatStep_hInit_031_Gen : nativeHeatInitGen 31 = nativeHeat031Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_031_Gen, nativeHeatStep_hVar_031_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat031Init00_formula
    · exact nativeHeat031Init01_formula
    · exact nativeHeat031Init02_formula
    · exact nativeHeat031Init03_formula
    · exact nativeHeat031Init04_formula
    · exact nativeHeat031Init05_formula
    · exact nativeHeat031Init06_formula
    · exact nativeHeat031Init07_formula
    · exact nativeHeat031Init08_formula
    · exact nativeHeat031Init09_formula
    · exact nativeHeat031Init10_formula
    · exact nativeHeat031Init11_formula
    · exact nativeHeat031Init12_formula
    · exact nativeHeat031Init13_formula
    · exact nativeHeat031Init14_formula
    · exact nativeHeat031Init15_formula
    · exact nativeHeat031Init16_formula
    · exact nativeHeat031Init17_formula
    · exact nativeHeat031Init18_formula
    · exact nativeHeat031Init19_formula
    · exact nativeHeat031Init20_formula
theorem nativeHeatStep_hBase_031_Gen : nativeHeatBaseGen 31 = nativeHeat031Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_031_Gen, nativeHeatStep_hInit_031_Gen, nativeHeat031Base_formula]

theorem nativeHeatStep_hFixed_031_Gen : nativeHeatFixedGen 31 = nativeHeat031Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_031_Gen, nativeHeatStep_hFr_031_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat031Fixed01_formula
    · exact nativeHeat031Fixed02_formula
    · exact nativeHeat031Fixed03_formula
    · exact nativeHeat031Fixed04_formula
    · exact nativeHeat031Fixed05_formula
    · exact nativeHeat031Fixed06_formula
    · exact nativeHeat031Fixed07_formula
    · exact nativeHeat031Fixed08_formula
    · exact nativeHeat031Fixed09_formula
    · exact nativeHeat031Fixed10_formula
    · exact nativeHeat031Fixed11_formula
    · exact nativeHeat031Fixed12_formula
    · exact nativeHeat031Fixed13_formula
    · exact nativeHeat031Fixed14_formula
    · exact nativeHeat031Fixed15_formula
    · exact nativeHeat031Fixed16_formula
    · exact nativeHeat031Fixed17_formula
    · exact nativeHeat031Fixed18_formula
    · exact nativeHeat031Fixed19_formula
    · exact nativeHeat031Fixed20_formula

theorem nativeHeatStep_chk_031_Gen :
    nativeHeatPassRootsOk nativeGap032Old nativeHeat031Frames nativeHeat031Coef nativeHeat031Fixed nativeHeat031Base 48 nativeHeat031Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_031_Gen : NativeHeatStepPassNum 31 := by
  refine nativeHeatStepPassNum_of_literals 31 nativeGap032Old nativeHeat031Frames (nativeHeatExpArg nativeGap032Old)
    nativeHeat031Exp nativeHeat031Coef nativeHeat031Fixed nativeHeat031Init nativeHeat031Base nativeHeatStep_hOld_031_Gen
    nativeHeatStep_hFr_031_Gen nativeHeatStep_hArg_031_Gen nativeHeatStep_hExp_031_Gen
    nativeHeatStep_hCoef_031_Gen nativeHeatStep_hFixed_031_Gen
    nativeHeatStep_hInit_031_Gen nativeHeatStep_hBase_031_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_031_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_031_Gen :
    nativeHeatY0Gen 31 = nativeShiftedFrame 1 (min nativeGap032Old.x nativeGap032Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_031_Gen, nativeHeatStep_hInd_031_Gen]

theorem nativeHeatStepFrameNum_031_Gen : NativeHeatStepFrameNum 31 := by
  have h1 := nativeHeatStep_hOld_031_Gen
  have h2 := nativeHeatStep_hInd_031_Gen
  have h3 := nativeHeatStep_hVar_031_Gen
  have h4 := nativeHeatStep_hQm_031_Gen
  have h5 := nativeHeatStep_hQN_031_Gen
  have h6 := nativeHeatStep_hY0_031_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_031_Gen : NativeHeatStepIndivNum 31 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 31 (by norm_num)) = nativeGap032Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_031_Gen]; exact nativeGap032Old_source
  · rw [hc, nativeHeatStep_hInd_031_Gen]; exact nativeGap032Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_031_Gen : nativeHeatY48Gen 31 = nativeHeat031Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_031_Gen, nativeHeatStep_hFr_031_Gen,
    nativeHeatStep_hCoef_031_Gen, nativeHeatStep_hFixed_031_Gen,
    nativeHeatStep_hBase_031_Gen]
  exact nativeHeat031All48

theorem nativeHeatResultGen_031 : nativeHeatResultGen 31 = nativeHeat031Result := by
  rw [← nativeHeat031Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_031_Gen, nativeHeatStep_hY0_031_Gen, nativeHeatStep_hExp_031_Gen,
    nativeHeatStep_hInit_031_Gen, nativeHeatStep_hFixed_031_Gen]

end ASDExplicitGamma.Native

end
