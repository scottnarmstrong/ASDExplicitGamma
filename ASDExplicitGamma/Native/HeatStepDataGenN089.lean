module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat089Complete
public import ASDExplicitGamma.Numerics.Native.Gap090Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_089_Gen : nativeHeatOldRowGen 89 = nativeGap090Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_089_Gen : nativeHeatIndividualGen 89 = nativeGap090Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_089_Gen : nativeHeatGenVariance 89 = nativeHeat089Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_089_Gen, nativeHeat089Variance_formula]

theorem nativeHeatStep_hSpec_089_Gen : nativeHeatGenSpectral 89 = nativeHeat089Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_089_Gen, nativeHeat089Variance_formula]

theorem nativeHeatStep_hQm_089_Gen : nativeHeatGenQm 89 = nativeHeat089Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_089_Gen, nativeHeatStep_hSpec_089_Gen,
    nativeHeat089Qm_formula]

theorem nativeHeatStep_hQN_089_Gen : nativeHeatQNGen 89 = nativeHeat089QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_089_Gen, nativeHeat089QN_formula]

theorem nativeHeatStep_hFr_089_Gen : nativeHeatFramesGen 89 = nativeHeat089Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_089_Gen, nativeHeatStep_hInd_089_Gen,
    nativeHeatStep_hVar_089_Gen, nativeHeatStep_hQN_089_Gen, nativeHeat089Frames_formula]

theorem nativeHeatStep_hArg_089_Gen : nativeHeatExpArgGen 89 = nativeHeatExpArg nativeGap090Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_089_Gen]

theorem nativeHeatStep_hExp_089_Gen : nativeHeatExpGen 89 = nativeHeat089Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_089_Gen, nativeHeat089Exp_formula]

theorem nativeHeatStep_hCoef_089_Gen : nativeHeatCoefGen 89 = nativeHeat089Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_089_Gen, nativeHeat089Coef_formula]

theorem nativeHeatStep_hInit_089_Gen : nativeHeatInitGen 89 = nativeHeat089Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_089_Gen, nativeHeatStep_hVar_089_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat089Init00_formula
    · exact nativeHeat089Init01_formula
    · exact nativeHeat089Init02_formula
    · exact nativeHeat089Init03_formula
    · exact nativeHeat089Init04_formula
    · exact nativeHeat089Init05_formula
    · exact nativeHeat089Init06_formula
    · exact nativeHeat089Init07_formula
    · exact nativeHeat089Init08_formula
    · exact nativeHeat089Init09_formula
    · exact nativeHeat089Init10_formula
    · exact nativeHeat089Init11_formula
    · exact nativeHeat089Init12_formula
    · exact nativeHeat089Init13_formula
    · exact nativeHeat089Init14_formula
    · exact nativeHeat089Init15_formula
    · exact nativeHeat089Init16_formula
    · exact nativeHeat089Init17_formula
    · exact nativeHeat089Init18_formula
    · exact nativeHeat089Init19_formula
    · exact nativeHeat089Init20_formula
theorem nativeHeatStep_hBase_089_Gen : nativeHeatBaseGen 89 = nativeHeat089Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_089_Gen, nativeHeatStep_hInit_089_Gen, nativeHeat089Base_formula]

theorem nativeHeatStep_hFixed_089_Gen : nativeHeatFixedGen 89 = nativeHeat089Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_089_Gen, nativeHeatStep_hFr_089_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat089Fixed01_formula
    · exact nativeHeat089Fixed02_formula
    · exact nativeHeat089Fixed03_formula
    · exact nativeHeat089Fixed04_formula
    · exact nativeHeat089Fixed05_formula
    · exact nativeHeat089Fixed06_formula
    · exact nativeHeat089Fixed07_formula
    · exact nativeHeat089Fixed08_formula
    · exact nativeHeat089Fixed09_formula
    · exact nativeHeat089Fixed10_formula
    · exact nativeHeat089Fixed11_formula
    · exact nativeHeat089Fixed12_formula
    · exact nativeHeat089Fixed13_formula
    · exact nativeHeat089Fixed14_formula
    · exact nativeHeat089Fixed15_formula
    · exact nativeHeat089Fixed16_formula
    · exact nativeHeat089Fixed17_formula
    · exact nativeHeat089Fixed18_formula
    · exact nativeHeat089Fixed19_formula
    · exact nativeHeat089Fixed20_formula

theorem nativeHeatStep_chk_089_Gen :
    nativeHeatPassRootsOk nativeGap090Old nativeHeat089Frames nativeHeat089Coef nativeHeat089Fixed nativeHeat089Base 48 nativeHeat089Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_089_Gen : NativeHeatStepPassNum 89 := by
  refine nativeHeatStepPassNum_of_literals 89 nativeGap090Old nativeHeat089Frames (nativeHeatExpArg nativeGap090Old)
    nativeHeat089Exp nativeHeat089Coef nativeHeat089Fixed nativeHeat089Init nativeHeat089Base nativeHeatStep_hOld_089_Gen
    nativeHeatStep_hFr_089_Gen nativeHeatStep_hArg_089_Gen nativeHeatStep_hExp_089_Gen
    nativeHeatStep_hCoef_089_Gen nativeHeatStep_hFixed_089_Gen
    nativeHeatStep_hInit_089_Gen nativeHeatStep_hBase_089_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_089_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_089_Gen :
    nativeHeatY0Gen 89 = nativeShiftedFrame 1 (min nativeGap090Old.x nativeGap090Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_089_Gen, nativeHeatStep_hInd_089_Gen]

theorem nativeHeatStepFrameNum_089_Gen : NativeHeatStepFrameNum 89 := by
  have h1 := nativeHeatStep_hOld_089_Gen
  have h2 := nativeHeatStep_hInd_089_Gen
  have h3 := nativeHeatStep_hVar_089_Gen
  have h4 := nativeHeatStep_hQm_089_Gen
  have h5 := nativeHeatStep_hQN_089_Gen
  have h6 := nativeHeatStep_hY0_089_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_089_Gen : NativeHeatStepIndivNum 89 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 89 (by norm_num)) = nativeGap090Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_089_Gen]; exact nativeGap090Old_source
  · rw [hc, nativeHeatStep_hInd_089_Gen]; exact nativeGap090Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_089_Gen : nativeHeatY48Gen 89 = nativeHeat089Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_089_Gen, nativeHeatStep_hFr_089_Gen,
    nativeHeatStep_hCoef_089_Gen, nativeHeatStep_hFixed_089_Gen,
    nativeHeatStep_hBase_089_Gen]
  exact nativeHeat089All48

theorem nativeHeatResultGen_089 : nativeHeatResultGen 89 = nativeHeat089Result := by
  rw [← nativeHeat089Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_089_Gen, nativeHeatStep_hY0_089_Gen, nativeHeatStep_hExp_089_Gen,
    nativeHeatStep_hInit_089_Gen, nativeHeatStep_hFixed_089_Gen]

end ASDExplicitGamma.Native

end
