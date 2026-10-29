module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat125Complete
public import ASDExplicitGamma.Numerics.Native.Gap126Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_125_Gen : nativeHeatOldRowGen 125 = nativeGap126Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_125_Gen : nativeHeatIndividualGen 125 = nativeGap126Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_125_Gen : nativeHeatGenVariance 125 = nativeHeat125Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_125_Gen, nativeHeat125Variance_formula]

theorem nativeHeatStep_hSpec_125_Gen : nativeHeatGenSpectral 125 = nativeHeat125Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_125_Gen, nativeHeat125Variance_formula]

theorem nativeHeatStep_hQm_125_Gen : nativeHeatGenQm 125 = nativeHeat125Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_125_Gen, nativeHeatStep_hSpec_125_Gen,
    nativeHeat125Qm_formula]

theorem nativeHeatStep_hQN_125_Gen : nativeHeatQNGen 125 = nativeHeat125QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_125_Gen, nativeHeat125QN_formula]

theorem nativeHeatStep_hFr_125_Gen : nativeHeatFramesGen 125 = nativeHeat125Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_125_Gen, nativeHeatStep_hInd_125_Gen,
    nativeHeatStep_hVar_125_Gen, nativeHeatStep_hQN_125_Gen, nativeHeat125Frames_formula]

theorem nativeHeatStep_hArg_125_Gen : nativeHeatExpArgGen 125 = nativeHeatExpArg nativeGap126Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_125_Gen]

theorem nativeHeatStep_hExp_125_Gen : nativeHeatExpGen 125 = nativeHeat125Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_125_Gen, nativeHeat125Exp_formula]

theorem nativeHeatStep_hCoef_125_Gen : nativeHeatCoefGen 125 = nativeHeat125Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_125_Gen, nativeHeat125Coef_formula]

theorem nativeHeatStep_hInit_125_Gen : nativeHeatInitGen 125 = nativeHeat125Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_125_Gen, nativeHeatStep_hVar_125_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat125Init00_formula
    · exact nativeHeat125Init01_formula
    · exact nativeHeat125Init02_formula
    · exact nativeHeat125Init03_formula
    · exact nativeHeat125Init04_formula
    · exact nativeHeat125Init05_formula
    · exact nativeHeat125Init06_formula
    · exact nativeHeat125Init07_formula
    · exact nativeHeat125Init08_formula
    · exact nativeHeat125Init09_formula
    · exact nativeHeat125Init10_formula
    · exact nativeHeat125Init11_formula
    · exact nativeHeat125Init12_formula
    · exact nativeHeat125Init13_formula
    · exact nativeHeat125Init14_formula
    · exact nativeHeat125Init15_formula
    · exact nativeHeat125Init16_formula
    · exact nativeHeat125Init17_formula
    · exact nativeHeat125Init18_formula
    · exact nativeHeat125Init19_formula
    · exact nativeHeat125Init20_formula
theorem nativeHeatStep_hBase_125_Gen : nativeHeatBaseGen 125 = nativeHeat125Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_125_Gen, nativeHeatStep_hInit_125_Gen, nativeHeat125Base_formula]

theorem nativeHeatStep_hFixed_125_Gen : nativeHeatFixedGen 125 = nativeHeat125Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_125_Gen, nativeHeatStep_hFr_125_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat125Fixed01_formula
    · exact nativeHeat125Fixed02_formula
    · exact nativeHeat125Fixed03_formula
    · exact nativeHeat125Fixed04_formula
    · exact nativeHeat125Fixed05_formula
    · exact nativeHeat125Fixed06_formula
    · exact nativeHeat125Fixed07_formula
    · exact nativeHeat125Fixed08_formula
    · exact nativeHeat125Fixed09_formula
    · exact nativeHeat125Fixed10_formula
    · exact nativeHeat125Fixed11_formula
    · exact nativeHeat125Fixed12_formula
    · exact nativeHeat125Fixed13_formula
    · exact nativeHeat125Fixed14_formula
    · exact nativeHeat125Fixed15_formula
    · exact nativeHeat125Fixed16_formula
    · exact nativeHeat125Fixed17_formula
    · exact nativeHeat125Fixed18_formula
    · exact nativeHeat125Fixed19_formula
    · exact nativeHeat125Fixed20_formula

theorem nativeHeatStep_chk_125_Gen :
    nativeHeatPassRootsOk nativeGap126Old nativeHeat125Frames nativeHeat125Coef nativeHeat125Fixed nativeHeat125Base 48 nativeHeat125Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_125_Gen : NativeHeatStepPassNum 125 := by
  refine nativeHeatStepPassNum_of_literals 125 nativeGap126Old nativeHeat125Frames (nativeHeatExpArg nativeGap126Old)
    nativeHeat125Exp nativeHeat125Coef nativeHeat125Fixed nativeHeat125Init nativeHeat125Base nativeHeatStep_hOld_125_Gen
    nativeHeatStep_hFr_125_Gen nativeHeatStep_hArg_125_Gen nativeHeatStep_hExp_125_Gen
    nativeHeatStep_hCoef_125_Gen nativeHeatStep_hFixed_125_Gen
    nativeHeatStep_hInit_125_Gen nativeHeatStep_hBase_125_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_125_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_125_Gen :
    nativeHeatY0Gen 125 = nativeShiftedFrame 1 (min nativeGap126Old.x nativeGap126Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_125_Gen, nativeHeatStep_hInd_125_Gen]

theorem nativeHeatStepFrameNum_125_Gen : NativeHeatStepFrameNum 125 := by
  have h1 := nativeHeatStep_hOld_125_Gen
  have h2 := nativeHeatStep_hInd_125_Gen
  have h3 := nativeHeatStep_hVar_125_Gen
  have h4 := nativeHeatStep_hQm_125_Gen
  have h5 := nativeHeatStep_hQN_125_Gen
  have h6 := nativeHeatStep_hY0_125_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_125_Gen : NativeHeatStepIndivNum 125 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 125 (by norm_num)) = nativeGap126Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_125_Gen]; exact nativeGap126Old_source
  · rw [hc, nativeHeatStep_hInd_125_Gen]; exact nativeGap126Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_125_Gen : nativeHeatY48Gen 125 = nativeHeat125Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_125_Gen, nativeHeatStep_hFr_125_Gen,
    nativeHeatStep_hCoef_125_Gen, nativeHeatStep_hFixed_125_Gen,
    nativeHeatStep_hBase_125_Gen]
  exact nativeHeat125All48

theorem nativeHeatResultGen_125 : nativeHeatResultGen 125 = nativeHeat125Result := by
  rw [← nativeHeat125Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_125_Gen, nativeHeatStep_hY0_125_Gen, nativeHeatStep_hExp_125_Gen,
    nativeHeatStep_hInit_125_Gen, nativeHeatStep_hFixed_125_Gen]

end ASDExplicitGamma.Native

end
