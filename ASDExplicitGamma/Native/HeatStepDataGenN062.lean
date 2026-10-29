module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat062Complete
public import ASDExplicitGamma.Numerics.Native.Gap063Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_062_Gen : nativeHeatOldRowGen 62 = nativeGap063Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_062_Gen : nativeHeatIndividualGen 62 = nativeGap063Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_062_Gen : nativeHeatGenVariance 62 = nativeHeat062Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_062_Gen, nativeHeat062Variance_formula]

theorem nativeHeatStep_hSpec_062_Gen : nativeHeatGenSpectral 62 = nativeHeat062Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_062_Gen, nativeHeat062Variance_formula]

theorem nativeHeatStep_hQm_062_Gen : nativeHeatGenQm 62 = nativeHeat062Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_062_Gen, nativeHeatStep_hSpec_062_Gen,
    nativeHeat062Qm_formula]

theorem nativeHeatStep_hQN_062_Gen : nativeHeatQNGen 62 = nativeHeat062QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_062_Gen, nativeHeat062QN_formula]

theorem nativeHeatStep_hFr_062_Gen : nativeHeatFramesGen 62 = nativeHeat062Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_062_Gen, nativeHeatStep_hInd_062_Gen,
    nativeHeatStep_hVar_062_Gen, nativeHeatStep_hQN_062_Gen, nativeHeat062Frames_formula]

theorem nativeHeatStep_hArg_062_Gen : nativeHeatExpArgGen 62 = nativeHeatExpArg nativeGap063Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_062_Gen]

theorem nativeHeatStep_hExp_062_Gen : nativeHeatExpGen 62 = nativeHeat062Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_062_Gen, nativeHeat062Exp_formula]

theorem nativeHeatStep_hCoef_062_Gen : nativeHeatCoefGen 62 = nativeHeat062Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_062_Gen, nativeHeat062Coef_formula]

theorem nativeHeatStep_hInit_062_Gen : nativeHeatInitGen 62 = nativeHeat062Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_062_Gen, nativeHeatStep_hVar_062_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat062Init00_formula
    · exact nativeHeat062Init01_formula
    · exact nativeHeat062Init02_formula
    · exact nativeHeat062Init03_formula
    · exact nativeHeat062Init04_formula
    · exact nativeHeat062Init05_formula
    · exact nativeHeat062Init06_formula
    · exact nativeHeat062Init07_formula
    · exact nativeHeat062Init08_formula
    · exact nativeHeat062Init09_formula
    · exact nativeHeat062Init10_formula
    · exact nativeHeat062Init11_formula
    · exact nativeHeat062Init12_formula
    · exact nativeHeat062Init13_formula
    · exact nativeHeat062Init14_formula
    · exact nativeHeat062Init15_formula
    · exact nativeHeat062Init16_formula
    · exact nativeHeat062Init17_formula
    · exact nativeHeat062Init18_formula
    · exact nativeHeat062Init19_formula
    · exact nativeHeat062Init20_formula
theorem nativeHeatStep_hBase_062_Gen : nativeHeatBaseGen 62 = nativeHeat062Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_062_Gen, nativeHeatStep_hInit_062_Gen, nativeHeat062Base_formula]

theorem nativeHeatStep_hFixed_062_Gen : nativeHeatFixedGen 62 = nativeHeat062Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_062_Gen, nativeHeatStep_hFr_062_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat062Fixed01_formula
    · exact nativeHeat062Fixed02_formula
    · exact nativeHeat062Fixed03_formula
    · exact nativeHeat062Fixed04_formula
    · exact nativeHeat062Fixed05_formula
    · exact nativeHeat062Fixed06_formula
    · exact nativeHeat062Fixed07_formula
    · exact nativeHeat062Fixed08_formula
    · exact nativeHeat062Fixed09_formula
    · exact nativeHeat062Fixed10_formula
    · exact nativeHeat062Fixed11_formula
    · exact nativeHeat062Fixed12_formula
    · exact nativeHeat062Fixed13_formula
    · exact nativeHeat062Fixed14_formula
    · exact nativeHeat062Fixed15_formula
    · exact nativeHeat062Fixed16_formula
    · exact nativeHeat062Fixed17_formula
    · exact nativeHeat062Fixed18_formula
    · exact nativeHeat062Fixed19_formula
    · exact nativeHeat062Fixed20_formula

theorem nativeHeatStep_chk_062_Gen :
    nativeHeatPassRootsOk nativeGap063Old nativeHeat062Frames nativeHeat062Coef nativeHeat062Fixed nativeHeat062Base 48 nativeHeat062Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_062_Gen : NativeHeatStepPassNum 62 := by
  refine nativeHeatStepPassNum_of_literals 62 nativeGap063Old nativeHeat062Frames (nativeHeatExpArg nativeGap063Old)
    nativeHeat062Exp nativeHeat062Coef nativeHeat062Fixed nativeHeat062Init nativeHeat062Base nativeHeatStep_hOld_062_Gen
    nativeHeatStep_hFr_062_Gen nativeHeatStep_hArg_062_Gen nativeHeatStep_hExp_062_Gen
    nativeHeatStep_hCoef_062_Gen nativeHeatStep_hFixed_062_Gen
    nativeHeatStep_hInit_062_Gen nativeHeatStep_hBase_062_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_062_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_062_Gen :
    nativeHeatY0Gen 62 = nativeShiftedFrame 1 (min nativeGap063Old.x nativeGap063Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_062_Gen, nativeHeatStep_hInd_062_Gen]

theorem nativeHeatStepFrameNum_062_Gen : NativeHeatStepFrameNum 62 := by
  have h1 := nativeHeatStep_hOld_062_Gen
  have h2 := nativeHeatStep_hInd_062_Gen
  have h3 := nativeHeatStep_hVar_062_Gen
  have h4 := nativeHeatStep_hQm_062_Gen
  have h5 := nativeHeatStep_hQN_062_Gen
  have h6 := nativeHeatStep_hY0_062_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_062_Gen : NativeHeatStepIndivNum 62 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 62 (by norm_num)) = nativeGap063Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_062_Gen]; exact nativeGap063Old_source
  · rw [hc, nativeHeatStep_hInd_062_Gen]; exact nativeGap063Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_062_Gen : nativeHeatY48Gen 62 = nativeHeat062Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_062_Gen, nativeHeatStep_hFr_062_Gen,
    nativeHeatStep_hCoef_062_Gen, nativeHeatStep_hFixed_062_Gen,
    nativeHeatStep_hBase_062_Gen]
  exact nativeHeat062All48

theorem nativeHeatResultGen_062 : nativeHeatResultGen 62 = nativeHeat062Result := by
  rw [← nativeHeat062Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_062_Gen, nativeHeatStep_hY0_062_Gen, nativeHeatStep_hExp_062_Gen,
    nativeHeatStep_hInit_062_Gen, nativeHeatStep_hFixed_062_Gen]

end ASDExplicitGamma.Native

end
