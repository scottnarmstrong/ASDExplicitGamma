module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat019Complete
public import ASDExplicitGamma.Numerics.Native.Gap020Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_019_Gen : nativeHeatOldRowGen 19 = nativeGap020Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_019_Gen : nativeHeatIndividualGen 19 = nativeGap020Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_019_Gen : nativeHeatGenVariance 19 = nativeHeat019Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_019_Gen, nativeHeat019Variance_formula]

theorem nativeHeatStep_hSpec_019_Gen : nativeHeatGenSpectral 19 = nativeHeat019Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_019_Gen, nativeHeat019Variance_formula]

theorem nativeHeatStep_hQm_019_Gen : nativeHeatGenQm 19 = nativeHeat019Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_019_Gen, nativeHeatStep_hSpec_019_Gen,
    nativeHeat019Qm_formula]

theorem nativeHeatStep_hQN_019_Gen : nativeHeatQNGen 19 = nativeHeat019QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_019_Gen, nativeHeat019QN_formula]

theorem nativeHeatStep_hFr_019_Gen : nativeHeatFramesGen 19 = nativeHeat019Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_019_Gen, nativeHeatStep_hInd_019_Gen,
    nativeHeatStep_hVar_019_Gen, nativeHeatStep_hQN_019_Gen, nativeHeat019Frames_formula]

theorem nativeHeatStep_hArg_019_Gen : nativeHeatExpArgGen 19 = nativeHeatExpArg nativeGap020Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_019_Gen]

theorem nativeHeatStep_hExp_019_Gen : nativeHeatExpGen 19 = nativeHeat019Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_019_Gen, nativeHeat019Exp_formula]

theorem nativeHeatStep_hCoef_019_Gen : nativeHeatCoefGen 19 = nativeHeat019Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_019_Gen, nativeHeat019Coef_formula]

theorem nativeHeatStep_hInit_019_Gen : nativeHeatInitGen 19 = nativeHeat019Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_019_Gen, nativeHeatStep_hVar_019_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat019Init00_formula
    · exact nativeHeat019Init01_formula
    · exact nativeHeat019Init02_formula
    · exact nativeHeat019Init03_formula
    · exact nativeHeat019Init04_formula
    · exact nativeHeat019Init05_formula
    · exact nativeHeat019Init06_formula
    · exact nativeHeat019Init07_formula
    · exact nativeHeat019Init08_formula
    · exact nativeHeat019Init09_formula
    · exact nativeHeat019Init10_formula
    · exact nativeHeat019Init11_formula
    · exact nativeHeat019Init12_formula
    · exact nativeHeat019Init13_formula
    · exact nativeHeat019Init14_formula
    · exact nativeHeat019Init15_formula
    · exact nativeHeat019Init16_formula
    · exact nativeHeat019Init17_formula
    · exact nativeHeat019Init18_formula
    · exact nativeHeat019Init19_formula
    · exact nativeHeat019Init20_formula
theorem nativeHeatStep_hBase_019_Gen : nativeHeatBaseGen 19 = nativeHeat019Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_019_Gen, nativeHeatStep_hInit_019_Gen, nativeHeat019Base_formula]

theorem nativeHeatStep_hFixed_019_Gen : nativeHeatFixedGen 19 = nativeHeat019Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_019_Gen, nativeHeatStep_hFr_019_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat019Fixed01_formula
    · exact nativeHeat019Fixed02_formula
    · exact nativeHeat019Fixed03_formula
    · exact nativeHeat019Fixed04_formula
    · exact nativeHeat019Fixed05_formula
    · exact nativeHeat019Fixed06_formula
    · exact nativeHeat019Fixed07_formula
    · exact nativeHeat019Fixed08_formula
    · exact nativeHeat019Fixed09_formula
    · exact nativeHeat019Fixed10_formula
    · exact nativeHeat019Fixed11_formula
    · exact nativeHeat019Fixed12_formula
    · exact nativeHeat019Fixed13_formula
    · exact nativeHeat019Fixed14_formula
    · exact nativeHeat019Fixed15_formula
    · exact nativeHeat019Fixed16_formula
    · exact nativeHeat019Fixed17_formula
    · exact nativeHeat019Fixed18_formula
    · exact nativeHeat019Fixed19_formula
    · exact nativeHeat019Fixed20_formula

theorem nativeHeatStep_chk_019_Gen :
    nativeHeatPassRootsOk nativeGap020Old nativeHeat019Frames nativeHeat019Coef nativeHeat019Fixed nativeHeat019Base 48 nativeHeat019Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_019_Gen : NativeHeatStepPassNum 19 := by
  refine nativeHeatStepPassNum_of_literals 19 nativeGap020Old nativeHeat019Frames (nativeHeatExpArg nativeGap020Old)
    nativeHeat019Exp nativeHeat019Coef nativeHeat019Fixed nativeHeat019Init nativeHeat019Base nativeHeatStep_hOld_019_Gen
    nativeHeatStep_hFr_019_Gen nativeHeatStep_hArg_019_Gen nativeHeatStep_hExp_019_Gen
    nativeHeatStep_hCoef_019_Gen nativeHeatStep_hFixed_019_Gen
    nativeHeatStep_hInit_019_Gen nativeHeatStep_hBase_019_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_019_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_019_Gen :
    nativeHeatY0Gen 19 = nativeShiftedFrame 1 (min nativeGap020Old.x nativeGap020Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_019_Gen, nativeHeatStep_hInd_019_Gen]

theorem nativeHeatStepFrameNum_019_Gen : NativeHeatStepFrameNum 19 := by
  have h1 := nativeHeatStep_hOld_019_Gen
  have h2 := nativeHeatStep_hInd_019_Gen
  have h3 := nativeHeatStep_hVar_019_Gen
  have h4 := nativeHeatStep_hQm_019_Gen
  have h5 := nativeHeatStep_hQN_019_Gen
  have h6 := nativeHeatStep_hY0_019_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_019_Gen : NativeHeatStepIndivNum 19 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 19 (by norm_num)) = nativeGap020Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_019_Gen]; exact nativeGap020Old_source
  · rw [hc, nativeHeatStep_hInd_019_Gen]; exact nativeGap020Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_019_Gen : nativeHeatY48Gen 19 = nativeHeat019Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_019_Gen, nativeHeatStep_hFr_019_Gen,
    nativeHeatStep_hCoef_019_Gen, nativeHeatStep_hFixed_019_Gen,
    nativeHeatStep_hBase_019_Gen]
  exact nativeHeat019All48

theorem nativeHeatResultGen_019 : nativeHeatResultGen 19 = nativeHeat019Result := by
  rw [← nativeHeat019Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_019_Gen, nativeHeatStep_hY0_019_Gen, nativeHeatStep_hExp_019_Gen,
    nativeHeatStep_hInit_019_Gen, nativeHeatStep_hFixed_019_Gen]

end ASDExplicitGamma.Native

end
