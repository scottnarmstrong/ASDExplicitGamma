module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat152Complete
public import ASDExplicitGamma.Numerics.Native.Gap153Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_152_Gen : nativeHeatOldRowGen 152 = nativeGap153Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_152_Gen : nativeHeatIndividualGen 152 = nativeGap153Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_152_Gen : nativeHeatGenVariance 152 = nativeHeat152Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_152_Gen, nativeHeat152Variance_formula]

theorem nativeHeatStep_hSpec_152_Gen : nativeHeatGenSpectral 152 = nativeHeat152Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_152_Gen, nativeHeat152Variance_formula]

theorem nativeHeatStep_hQm_152_Gen : nativeHeatGenQm 152 = nativeHeat152Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_152_Gen, nativeHeatStep_hSpec_152_Gen,
    nativeHeat152Qm_formula]

theorem nativeHeatStep_hQN_152_Gen : nativeHeatQNGen 152 = nativeHeat152QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_152_Gen, nativeHeat152QN_formula]

theorem nativeHeatStep_hFr_152_Gen : nativeHeatFramesGen 152 = nativeHeat152Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_152_Gen, nativeHeatStep_hInd_152_Gen,
    nativeHeatStep_hVar_152_Gen, nativeHeatStep_hQN_152_Gen, nativeHeat152Frames_formula]

theorem nativeHeatStep_hArg_152_Gen : nativeHeatExpArgGen 152 = nativeHeatExpArg nativeGap153Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_152_Gen]

theorem nativeHeatStep_hExp_152_Gen : nativeHeatExpGen 152 = nativeHeat152Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_152_Gen, nativeHeat152Exp_formula]

theorem nativeHeatStep_hCoef_152_Gen : nativeHeatCoefGen 152 = nativeHeat152Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_152_Gen, nativeHeat152Coef_formula]

theorem nativeHeatStep_hInit_152_Gen : nativeHeatInitGen 152 = nativeHeat152Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_152_Gen, nativeHeatStep_hVar_152_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat152Init00_formula
    · exact nativeHeat152Init01_formula
    · exact nativeHeat152Init02_formula
    · exact nativeHeat152Init03_formula
    · exact nativeHeat152Init04_formula
    · exact nativeHeat152Init05_formula
    · exact nativeHeat152Init06_formula
    · exact nativeHeat152Init07_formula
    · exact nativeHeat152Init08_formula
    · exact nativeHeat152Init09_formula
    · exact nativeHeat152Init10_formula
    · exact nativeHeat152Init11_formula
    · exact nativeHeat152Init12_formula
    · exact nativeHeat152Init13_formula
    · exact nativeHeat152Init14_formula
    · exact nativeHeat152Init15_formula
    · exact nativeHeat152Init16_formula
    · exact nativeHeat152Init17_formula
    · exact nativeHeat152Init18_formula
    · exact nativeHeat152Init19_formula
    · exact nativeHeat152Init20_formula
theorem nativeHeatStep_hBase_152_Gen : nativeHeatBaseGen 152 = nativeHeat152Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_152_Gen, nativeHeatStep_hInit_152_Gen, nativeHeat152Base_formula]

theorem nativeHeatStep_hFixed_152_Gen : nativeHeatFixedGen 152 = nativeHeat152Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_152_Gen, nativeHeatStep_hFr_152_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat152Fixed01_formula
    · exact nativeHeat152Fixed02_formula
    · exact nativeHeat152Fixed03_formula
    · exact nativeHeat152Fixed04_formula
    · exact nativeHeat152Fixed05_formula
    · exact nativeHeat152Fixed06_formula
    · exact nativeHeat152Fixed07_formula
    · exact nativeHeat152Fixed08_formula
    · exact nativeHeat152Fixed09_formula
    · exact nativeHeat152Fixed10_formula
    · exact nativeHeat152Fixed11_formula
    · exact nativeHeat152Fixed12_formula
    · exact nativeHeat152Fixed13_formula
    · exact nativeHeat152Fixed14_formula
    · exact nativeHeat152Fixed15_formula
    · exact nativeHeat152Fixed16_formula
    · exact nativeHeat152Fixed17_formula
    · exact nativeHeat152Fixed18_formula
    · exact nativeHeat152Fixed19_formula
    · exact nativeHeat152Fixed20_formula

theorem nativeHeatStep_chk_152_Gen :
    nativeHeatPassRootsOk nativeGap153Old nativeHeat152Frames nativeHeat152Coef nativeHeat152Fixed nativeHeat152Base 48 nativeHeat152Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_152_Gen : NativeHeatStepPassNum 152 := by
  refine nativeHeatStepPassNum_of_literals 152 nativeGap153Old nativeHeat152Frames (nativeHeatExpArg nativeGap153Old)
    nativeHeat152Exp nativeHeat152Coef nativeHeat152Fixed nativeHeat152Init nativeHeat152Base nativeHeatStep_hOld_152_Gen
    nativeHeatStep_hFr_152_Gen nativeHeatStep_hArg_152_Gen nativeHeatStep_hExp_152_Gen
    nativeHeatStep_hCoef_152_Gen nativeHeatStep_hFixed_152_Gen
    nativeHeatStep_hInit_152_Gen nativeHeatStep_hBase_152_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_152_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_152_Gen :
    nativeHeatY0Gen 152 = nativeShiftedFrame 1 (min nativeGap153Old.x nativeGap153Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_152_Gen, nativeHeatStep_hInd_152_Gen]

theorem nativeHeatStepFrameNum_152_Gen : NativeHeatStepFrameNum 152 := by
  have h1 := nativeHeatStep_hOld_152_Gen
  have h2 := nativeHeatStep_hInd_152_Gen
  have h3 := nativeHeatStep_hVar_152_Gen
  have h4 := nativeHeatStep_hQm_152_Gen
  have h5 := nativeHeatStep_hQN_152_Gen
  have h6 := nativeHeatStep_hY0_152_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_152_Gen : NativeHeatStepIndivNum 152 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 152 (by norm_num)) = nativeGap153Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_152_Gen]; exact nativeGap153Old_source
  · rw [hc, nativeHeatStep_hInd_152_Gen]; exact nativeGap153Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_152_Gen : nativeHeatY48Gen 152 = nativeHeat152Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_152_Gen, nativeHeatStep_hFr_152_Gen,
    nativeHeatStep_hCoef_152_Gen, nativeHeatStep_hFixed_152_Gen,
    nativeHeatStep_hBase_152_Gen]
  exact nativeHeat152All48

theorem nativeHeatResultGen_152 : nativeHeatResultGen 152 = nativeHeat152Result := by
  rw [← nativeHeat152Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_152_Gen, nativeHeatStep_hY0_152_Gen, nativeHeatStep_hExp_152_Gen,
    nativeHeatStep_hInit_152_Gen, nativeHeatStep_hFixed_152_Gen]

end ASDExplicitGamma.Native

end
