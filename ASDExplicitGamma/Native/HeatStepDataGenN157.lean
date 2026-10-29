module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat157Complete
public import ASDExplicitGamma.Numerics.Native.Gap158Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_157_Gen : nativeHeatOldRowGen 157 = nativeGap158Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_157_Gen : nativeHeatIndividualGen 157 = nativeGap158Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_157_Gen : nativeHeatGenVariance 157 = nativeHeat157Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_157_Gen, nativeHeat157Variance_formula]

theorem nativeHeatStep_hSpec_157_Gen : nativeHeatGenSpectral 157 = nativeHeat157Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_157_Gen, nativeHeat157Variance_formula]

theorem nativeHeatStep_hQm_157_Gen : nativeHeatGenQm 157 = nativeHeat157Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_157_Gen, nativeHeatStep_hSpec_157_Gen,
    nativeHeat157Qm_formula]

theorem nativeHeatStep_hQN_157_Gen : nativeHeatQNGen 157 = nativeHeat157QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_157_Gen, nativeHeat157QN_formula]

theorem nativeHeatStep_hFr_157_Gen : nativeHeatFramesGen 157 = nativeHeat157Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_157_Gen, nativeHeatStep_hInd_157_Gen,
    nativeHeatStep_hVar_157_Gen, nativeHeatStep_hQN_157_Gen, nativeHeat157Frames_formula]

theorem nativeHeatStep_hArg_157_Gen : nativeHeatExpArgGen 157 = nativeHeatExpArg nativeGap158Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_157_Gen]

theorem nativeHeatStep_hExp_157_Gen : nativeHeatExpGen 157 = nativeHeat157Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_157_Gen, nativeHeat157Exp_formula]

theorem nativeHeatStep_hCoef_157_Gen : nativeHeatCoefGen 157 = nativeHeat157Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_157_Gen, nativeHeat157Coef_formula]

theorem nativeHeatStep_hInit_157_Gen : nativeHeatInitGen 157 = nativeHeat157Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_157_Gen, nativeHeatStep_hVar_157_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat157Init00_formula
    · exact nativeHeat157Init01_formula
    · exact nativeHeat157Init02_formula
    · exact nativeHeat157Init03_formula
    · exact nativeHeat157Init04_formula
    · exact nativeHeat157Init05_formula
    · exact nativeHeat157Init06_formula
    · exact nativeHeat157Init07_formula
    · exact nativeHeat157Init08_formula
    · exact nativeHeat157Init09_formula
    · exact nativeHeat157Init10_formula
    · exact nativeHeat157Init11_formula
    · exact nativeHeat157Init12_formula
    · exact nativeHeat157Init13_formula
    · exact nativeHeat157Init14_formula
    · exact nativeHeat157Init15_formula
    · exact nativeHeat157Init16_formula
    · exact nativeHeat157Init17_formula
    · exact nativeHeat157Init18_formula
    · exact nativeHeat157Init19_formula
    · exact nativeHeat157Init20_formula
theorem nativeHeatStep_hBase_157_Gen : nativeHeatBaseGen 157 = nativeHeat157Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_157_Gen, nativeHeatStep_hInit_157_Gen, nativeHeat157Base_formula]

theorem nativeHeatStep_hFixed_157_Gen : nativeHeatFixedGen 157 = nativeHeat157Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_157_Gen, nativeHeatStep_hFr_157_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat157Fixed01_formula
    · exact nativeHeat157Fixed02_formula
    · exact nativeHeat157Fixed03_formula
    · exact nativeHeat157Fixed04_formula
    · exact nativeHeat157Fixed05_formula
    · exact nativeHeat157Fixed06_formula
    · exact nativeHeat157Fixed07_formula
    · exact nativeHeat157Fixed08_formula
    · exact nativeHeat157Fixed09_formula
    · exact nativeHeat157Fixed10_formula
    · exact nativeHeat157Fixed11_formula
    · exact nativeHeat157Fixed12_formula
    · exact nativeHeat157Fixed13_formula
    · exact nativeHeat157Fixed14_formula
    · exact nativeHeat157Fixed15_formula
    · exact nativeHeat157Fixed16_formula
    · exact nativeHeat157Fixed17_formula
    · exact nativeHeat157Fixed18_formula
    · exact nativeHeat157Fixed19_formula
    · exact nativeHeat157Fixed20_formula

theorem nativeHeatStep_chk_157_Gen :
    nativeHeatPassRootsOk nativeGap158Old nativeHeat157Frames nativeHeat157Coef nativeHeat157Fixed nativeHeat157Base 48 nativeHeat157Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_157_Gen : NativeHeatStepPassNum 157 := by
  refine nativeHeatStepPassNum_of_literals 157 nativeGap158Old nativeHeat157Frames (nativeHeatExpArg nativeGap158Old)
    nativeHeat157Exp nativeHeat157Coef nativeHeat157Fixed nativeHeat157Init nativeHeat157Base nativeHeatStep_hOld_157_Gen
    nativeHeatStep_hFr_157_Gen nativeHeatStep_hArg_157_Gen nativeHeatStep_hExp_157_Gen
    nativeHeatStep_hCoef_157_Gen nativeHeatStep_hFixed_157_Gen
    nativeHeatStep_hInit_157_Gen nativeHeatStep_hBase_157_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_157_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_157_Gen :
    nativeHeatY0Gen 157 = nativeShiftedFrame 1 (min nativeGap158Old.x nativeGap158Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_157_Gen, nativeHeatStep_hInd_157_Gen]

theorem nativeHeatStepFrameNum_157_Gen : NativeHeatStepFrameNum 157 := by
  have h1 := nativeHeatStep_hOld_157_Gen
  have h2 := nativeHeatStep_hInd_157_Gen
  have h3 := nativeHeatStep_hVar_157_Gen
  have h4 := nativeHeatStep_hQm_157_Gen
  have h5 := nativeHeatStep_hQN_157_Gen
  have h6 := nativeHeatStep_hY0_157_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_157_Gen : NativeHeatStepIndivNum 157 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 157 (by norm_num)) = nativeGap158Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_157_Gen]; exact nativeGap158Old_source
  · rw [hc, nativeHeatStep_hInd_157_Gen]; exact nativeGap158Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_157_Gen : nativeHeatY48Gen 157 = nativeHeat157Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_157_Gen, nativeHeatStep_hFr_157_Gen,
    nativeHeatStep_hCoef_157_Gen, nativeHeatStep_hFixed_157_Gen,
    nativeHeatStep_hBase_157_Gen]
  exact nativeHeat157All48

theorem nativeHeatResultGen_157 : nativeHeatResultGen 157 = nativeHeat157Result := by
  rw [← nativeHeat157Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_157_Gen, nativeHeatStep_hY0_157_Gen, nativeHeatStep_hExp_157_Gen,
    nativeHeatStep_hInit_157_Gen, nativeHeatStep_hFixed_157_Gen]

end ASDExplicitGamma.Native

end
