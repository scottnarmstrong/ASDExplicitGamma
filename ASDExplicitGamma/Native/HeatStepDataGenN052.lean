module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat052Complete
public import ASDExplicitGamma.Numerics.Native.Gap053Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_052_Gen : nativeHeatOldRowGen 52 = nativeGap053Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_052_Gen : nativeHeatIndividualGen 52 = nativeGap053Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_052_Gen : nativeHeatGenVariance 52 = nativeHeat052Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_052_Gen, nativeHeat052Variance_formula]

theorem nativeHeatStep_hSpec_052_Gen : nativeHeatGenSpectral 52 = nativeHeat052Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_052_Gen, nativeHeat052Variance_formula]

theorem nativeHeatStep_hQm_052_Gen : nativeHeatGenQm 52 = nativeHeat052Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_052_Gen, nativeHeatStep_hSpec_052_Gen,
    nativeHeat052Qm_formula]

theorem nativeHeatStep_hQN_052_Gen : nativeHeatQNGen 52 = nativeHeat052QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_052_Gen, nativeHeat052QN_formula]

theorem nativeHeatStep_hFr_052_Gen : nativeHeatFramesGen 52 = nativeHeat052Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_052_Gen, nativeHeatStep_hInd_052_Gen,
    nativeHeatStep_hVar_052_Gen, nativeHeatStep_hQN_052_Gen, nativeHeat052Frames_formula]

theorem nativeHeatStep_hArg_052_Gen : nativeHeatExpArgGen 52 = nativeHeatExpArg nativeGap053Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_052_Gen]

theorem nativeHeatStep_hExp_052_Gen : nativeHeatExpGen 52 = nativeHeat052Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_052_Gen, nativeHeat052Exp_formula]

theorem nativeHeatStep_hCoef_052_Gen : nativeHeatCoefGen 52 = nativeHeat052Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_052_Gen, nativeHeat052Coef_formula]

theorem nativeHeatStep_hInit_052_Gen : nativeHeatInitGen 52 = nativeHeat052Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_052_Gen, nativeHeatStep_hVar_052_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat052Init00_formula
    · exact nativeHeat052Init01_formula
    · exact nativeHeat052Init02_formula
    · exact nativeHeat052Init03_formula
    · exact nativeHeat052Init04_formula
    · exact nativeHeat052Init05_formula
    · exact nativeHeat052Init06_formula
    · exact nativeHeat052Init07_formula
    · exact nativeHeat052Init08_formula
    · exact nativeHeat052Init09_formula
    · exact nativeHeat052Init10_formula
    · exact nativeHeat052Init11_formula
    · exact nativeHeat052Init12_formula
    · exact nativeHeat052Init13_formula
    · exact nativeHeat052Init14_formula
    · exact nativeHeat052Init15_formula
    · exact nativeHeat052Init16_formula
    · exact nativeHeat052Init17_formula
    · exact nativeHeat052Init18_formula
    · exact nativeHeat052Init19_formula
    · exact nativeHeat052Init20_formula
theorem nativeHeatStep_hBase_052_Gen : nativeHeatBaseGen 52 = nativeHeat052Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_052_Gen, nativeHeatStep_hInit_052_Gen, nativeHeat052Base_formula]

theorem nativeHeatStep_hFixed_052_Gen : nativeHeatFixedGen 52 = nativeHeat052Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_052_Gen, nativeHeatStep_hFr_052_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat052Fixed01_formula
    · exact nativeHeat052Fixed02_formula
    · exact nativeHeat052Fixed03_formula
    · exact nativeHeat052Fixed04_formula
    · exact nativeHeat052Fixed05_formula
    · exact nativeHeat052Fixed06_formula
    · exact nativeHeat052Fixed07_formula
    · exact nativeHeat052Fixed08_formula
    · exact nativeHeat052Fixed09_formula
    · exact nativeHeat052Fixed10_formula
    · exact nativeHeat052Fixed11_formula
    · exact nativeHeat052Fixed12_formula
    · exact nativeHeat052Fixed13_formula
    · exact nativeHeat052Fixed14_formula
    · exact nativeHeat052Fixed15_formula
    · exact nativeHeat052Fixed16_formula
    · exact nativeHeat052Fixed17_formula
    · exact nativeHeat052Fixed18_formula
    · exact nativeHeat052Fixed19_formula
    · exact nativeHeat052Fixed20_formula

theorem nativeHeatStep_chk_052_Gen :
    nativeHeatPassRootsOk nativeGap053Old nativeHeat052Frames nativeHeat052Coef nativeHeat052Fixed nativeHeat052Base 48 nativeHeat052Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_052_Gen : NativeHeatStepPassNum 52 := by
  refine nativeHeatStepPassNum_of_literals 52 nativeGap053Old nativeHeat052Frames (nativeHeatExpArg nativeGap053Old)
    nativeHeat052Exp nativeHeat052Coef nativeHeat052Fixed nativeHeat052Init nativeHeat052Base nativeHeatStep_hOld_052_Gen
    nativeHeatStep_hFr_052_Gen nativeHeatStep_hArg_052_Gen nativeHeatStep_hExp_052_Gen
    nativeHeatStep_hCoef_052_Gen nativeHeatStep_hFixed_052_Gen
    nativeHeatStep_hInit_052_Gen nativeHeatStep_hBase_052_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_052_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_052_Gen :
    nativeHeatY0Gen 52 = nativeShiftedFrame 1 (min nativeGap053Old.x nativeGap053Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_052_Gen, nativeHeatStep_hInd_052_Gen]

theorem nativeHeatStepFrameNum_052_Gen : NativeHeatStepFrameNum 52 := by
  have h1 := nativeHeatStep_hOld_052_Gen
  have h2 := nativeHeatStep_hInd_052_Gen
  have h3 := nativeHeatStep_hVar_052_Gen
  have h4 := nativeHeatStep_hQm_052_Gen
  have h5 := nativeHeatStep_hQN_052_Gen
  have h6 := nativeHeatStep_hY0_052_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_052_Gen : NativeHeatStepIndivNum 52 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 52 (by norm_num)) = nativeGap053Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_052_Gen]; exact nativeGap053Old_source
  · rw [hc, nativeHeatStep_hInd_052_Gen]; exact nativeGap053Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_052_Gen : nativeHeatY48Gen 52 = nativeHeat052Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_052_Gen, nativeHeatStep_hFr_052_Gen,
    nativeHeatStep_hCoef_052_Gen, nativeHeatStep_hFixed_052_Gen,
    nativeHeatStep_hBase_052_Gen]
  exact nativeHeat052All48

theorem nativeHeatResultGen_052 : nativeHeatResultGen 52 = nativeHeat052Result := by
  rw [← nativeHeat052Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_052_Gen, nativeHeatStep_hY0_052_Gen, nativeHeatStep_hExp_052_Gen,
    nativeHeatStep_hInit_052_Gen, nativeHeatStep_hFixed_052_Gen]

end ASDExplicitGamma.Native

end
