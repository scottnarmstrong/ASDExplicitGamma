module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat039Complete
public import ASDExplicitGamma.Numerics.Native.Gap040Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_039_Gen : nativeHeatOldRowGen 39 = nativeGap040Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_039_Gen : nativeHeatIndividualGen 39 = nativeGap040Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_039_Gen : nativeHeatGenVariance 39 = nativeHeat039Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_039_Gen, nativeHeat039Variance_formula]

theorem nativeHeatStep_hSpec_039_Gen : nativeHeatGenSpectral 39 = nativeHeat039Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_039_Gen, nativeHeat039Variance_formula]

theorem nativeHeatStep_hQm_039_Gen : nativeHeatGenQm 39 = nativeHeat039Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_039_Gen, nativeHeatStep_hSpec_039_Gen,
    nativeHeat039Qm_formula]

theorem nativeHeatStep_hQN_039_Gen : nativeHeatQNGen 39 = nativeHeat039QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_039_Gen, nativeHeat039QN_formula]

theorem nativeHeatStep_hFr_039_Gen : nativeHeatFramesGen 39 = nativeHeat039Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_039_Gen, nativeHeatStep_hInd_039_Gen,
    nativeHeatStep_hVar_039_Gen, nativeHeatStep_hQN_039_Gen, nativeHeat039Frames_formula]

theorem nativeHeatStep_hArg_039_Gen : nativeHeatExpArgGen 39 = nativeHeatExpArg nativeGap040Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_039_Gen]

theorem nativeHeatStep_hExp_039_Gen : nativeHeatExpGen 39 = nativeHeat039Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_039_Gen, nativeHeat039Exp_formula]

theorem nativeHeatStep_hCoef_039_Gen : nativeHeatCoefGen 39 = nativeHeat039Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_039_Gen, nativeHeat039Coef_formula]

theorem nativeHeatStep_hInit_039_Gen : nativeHeatInitGen 39 = nativeHeat039Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_039_Gen, nativeHeatStep_hVar_039_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat039Init00_formula
    · exact nativeHeat039Init01_formula
    · exact nativeHeat039Init02_formula
    · exact nativeHeat039Init03_formula
    · exact nativeHeat039Init04_formula
    · exact nativeHeat039Init05_formula
    · exact nativeHeat039Init06_formula
    · exact nativeHeat039Init07_formula
    · exact nativeHeat039Init08_formula
    · exact nativeHeat039Init09_formula
    · exact nativeHeat039Init10_formula
    · exact nativeHeat039Init11_formula
    · exact nativeHeat039Init12_formula
    · exact nativeHeat039Init13_formula
    · exact nativeHeat039Init14_formula
    · exact nativeHeat039Init15_formula
    · exact nativeHeat039Init16_formula
    · exact nativeHeat039Init17_formula
    · exact nativeHeat039Init18_formula
    · exact nativeHeat039Init19_formula
    · exact nativeHeat039Init20_formula
theorem nativeHeatStep_hBase_039_Gen : nativeHeatBaseGen 39 = nativeHeat039Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_039_Gen, nativeHeatStep_hInit_039_Gen, nativeHeat039Base_formula]

theorem nativeHeatStep_hFixed_039_Gen : nativeHeatFixedGen 39 = nativeHeat039Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_039_Gen, nativeHeatStep_hFr_039_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat039Fixed01_formula
    · exact nativeHeat039Fixed02_formula
    · exact nativeHeat039Fixed03_formula
    · exact nativeHeat039Fixed04_formula
    · exact nativeHeat039Fixed05_formula
    · exact nativeHeat039Fixed06_formula
    · exact nativeHeat039Fixed07_formula
    · exact nativeHeat039Fixed08_formula
    · exact nativeHeat039Fixed09_formula
    · exact nativeHeat039Fixed10_formula
    · exact nativeHeat039Fixed11_formula
    · exact nativeHeat039Fixed12_formula
    · exact nativeHeat039Fixed13_formula
    · exact nativeHeat039Fixed14_formula
    · exact nativeHeat039Fixed15_formula
    · exact nativeHeat039Fixed16_formula
    · exact nativeHeat039Fixed17_formula
    · exact nativeHeat039Fixed18_formula
    · exact nativeHeat039Fixed19_formula
    · exact nativeHeat039Fixed20_formula

theorem nativeHeatStep_chk_039_Gen :
    nativeHeatPassRootsOk nativeGap040Old nativeHeat039Frames nativeHeat039Coef nativeHeat039Fixed nativeHeat039Base 48 nativeHeat039Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_039_Gen : NativeHeatStepPassNum 39 := by
  refine nativeHeatStepPassNum_of_literals 39 nativeGap040Old nativeHeat039Frames (nativeHeatExpArg nativeGap040Old)
    nativeHeat039Exp nativeHeat039Coef nativeHeat039Fixed nativeHeat039Init nativeHeat039Base nativeHeatStep_hOld_039_Gen
    nativeHeatStep_hFr_039_Gen nativeHeatStep_hArg_039_Gen nativeHeatStep_hExp_039_Gen
    nativeHeatStep_hCoef_039_Gen nativeHeatStep_hFixed_039_Gen
    nativeHeatStep_hInit_039_Gen nativeHeatStep_hBase_039_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_039_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_039_Gen :
    nativeHeatY0Gen 39 = nativeShiftedFrame 1 (min nativeGap040Old.x nativeGap040Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_039_Gen, nativeHeatStep_hInd_039_Gen]

theorem nativeHeatStepFrameNum_039_Gen : NativeHeatStepFrameNum 39 := by
  have h1 := nativeHeatStep_hOld_039_Gen
  have h2 := nativeHeatStep_hInd_039_Gen
  have h3 := nativeHeatStep_hVar_039_Gen
  have h4 := nativeHeatStep_hQm_039_Gen
  have h5 := nativeHeatStep_hQN_039_Gen
  have h6 := nativeHeatStep_hY0_039_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_039_Gen : NativeHeatStepIndivNum 39 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 39 (by norm_num)) = nativeGap040Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_039_Gen]; exact nativeGap040Old_source
  · rw [hc, nativeHeatStep_hInd_039_Gen]; exact nativeGap040Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_039_Gen : nativeHeatY48Gen 39 = nativeHeat039Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_039_Gen, nativeHeatStep_hFr_039_Gen,
    nativeHeatStep_hCoef_039_Gen, nativeHeatStep_hFixed_039_Gen,
    nativeHeatStep_hBase_039_Gen]
  exact nativeHeat039All48

theorem nativeHeatResultGen_039 : nativeHeatResultGen 39 = nativeHeat039Result := by
  rw [← nativeHeat039Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_039_Gen, nativeHeatStep_hY0_039_Gen, nativeHeatStep_hExp_039_Gen,
    nativeHeatStep_hInit_039_Gen, nativeHeatStep_hFixed_039_Gen]

end ASDExplicitGamma.Native

end
