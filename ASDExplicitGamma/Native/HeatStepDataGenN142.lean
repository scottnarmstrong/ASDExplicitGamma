module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat142Complete
public import ASDExplicitGamma.Numerics.Native.Gap143Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_142_Gen : nativeHeatOldRowGen 142 = nativeGap143Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_142_Gen : nativeHeatIndividualGen 142 = nativeGap143Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_142_Gen : nativeHeatGenVariance 142 = nativeHeat142Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_142_Gen, nativeHeat142Variance_formula]

theorem nativeHeatStep_hSpec_142_Gen : nativeHeatGenSpectral 142 = nativeHeat142Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_142_Gen, nativeHeat142Variance_formula]

theorem nativeHeatStep_hQm_142_Gen : nativeHeatGenQm 142 = nativeHeat142Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_142_Gen, nativeHeatStep_hSpec_142_Gen,
    nativeHeat142Qm_formula]

theorem nativeHeatStep_hQN_142_Gen : nativeHeatQNGen 142 = nativeHeat142QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_142_Gen, nativeHeat142QN_formula]

theorem nativeHeatStep_hFr_142_Gen : nativeHeatFramesGen 142 = nativeHeat142Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_142_Gen, nativeHeatStep_hInd_142_Gen,
    nativeHeatStep_hVar_142_Gen, nativeHeatStep_hQN_142_Gen, nativeHeat142Frames_formula]

theorem nativeHeatStep_hArg_142_Gen : nativeHeatExpArgGen 142 = nativeHeatExpArg nativeGap143Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_142_Gen]

theorem nativeHeatStep_hExp_142_Gen : nativeHeatExpGen 142 = nativeHeat142Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_142_Gen, nativeHeat142Exp_formula]

theorem nativeHeatStep_hCoef_142_Gen : nativeHeatCoefGen 142 = nativeHeat142Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_142_Gen, nativeHeat142Coef_formula]

theorem nativeHeatStep_hInit_142_Gen : nativeHeatInitGen 142 = nativeHeat142Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_142_Gen, nativeHeatStep_hVar_142_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat142Init00_formula
    · exact nativeHeat142Init01_formula
    · exact nativeHeat142Init02_formula
    · exact nativeHeat142Init03_formula
    · exact nativeHeat142Init04_formula
    · exact nativeHeat142Init05_formula
    · exact nativeHeat142Init06_formula
    · exact nativeHeat142Init07_formula
    · exact nativeHeat142Init08_formula
    · exact nativeHeat142Init09_formula
    · exact nativeHeat142Init10_formula
    · exact nativeHeat142Init11_formula
    · exact nativeHeat142Init12_formula
    · exact nativeHeat142Init13_formula
    · exact nativeHeat142Init14_formula
    · exact nativeHeat142Init15_formula
    · exact nativeHeat142Init16_formula
    · exact nativeHeat142Init17_formula
    · exact nativeHeat142Init18_formula
    · exact nativeHeat142Init19_formula
    · exact nativeHeat142Init20_formula
theorem nativeHeatStep_hBase_142_Gen : nativeHeatBaseGen 142 = nativeHeat142Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_142_Gen, nativeHeatStep_hInit_142_Gen, nativeHeat142Base_formula]

theorem nativeHeatStep_hFixed_142_Gen : nativeHeatFixedGen 142 = nativeHeat142Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_142_Gen, nativeHeatStep_hFr_142_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat142Fixed01_formula
    · exact nativeHeat142Fixed02_formula
    · exact nativeHeat142Fixed03_formula
    · exact nativeHeat142Fixed04_formula
    · exact nativeHeat142Fixed05_formula
    · exact nativeHeat142Fixed06_formula
    · exact nativeHeat142Fixed07_formula
    · exact nativeHeat142Fixed08_formula
    · exact nativeHeat142Fixed09_formula
    · exact nativeHeat142Fixed10_formula
    · exact nativeHeat142Fixed11_formula
    · exact nativeHeat142Fixed12_formula
    · exact nativeHeat142Fixed13_formula
    · exact nativeHeat142Fixed14_formula
    · exact nativeHeat142Fixed15_formula
    · exact nativeHeat142Fixed16_formula
    · exact nativeHeat142Fixed17_formula
    · exact nativeHeat142Fixed18_formula
    · exact nativeHeat142Fixed19_formula
    · exact nativeHeat142Fixed20_formula

theorem nativeHeatStep_chk_142_Gen :
    nativeHeatPassRootsOk nativeGap143Old nativeHeat142Frames nativeHeat142Coef nativeHeat142Fixed nativeHeat142Base 48 nativeHeat142Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_142_Gen : NativeHeatStepPassNum 142 := by
  refine nativeHeatStepPassNum_of_literals 142 nativeGap143Old nativeHeat142Frames (nativeHeatExpArg nativeGap143Old)
    nativeHeat142Exp nativeHeat142Coef nativeHeat142Fixed nativeHeat142Init nativeHeat142Base nativeHeatStep_hOld_142_Gen
    nativeHeatStep_hFr_142_Gen nativeHeatStep_hArg_142_Gen nativeHeatStep_hExp_142_Gen
    nativeHeatStep_hCoef_142_Gen nativeHeatStep_hFixed_142_Gen
    nativeHeatStep_hInit_142_Gen nativeHeatStep_hBase_142_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_142_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_142_Gen :
    nativeHeatY0Gen 142 = nativeShiftedFrame 1 (min nativeGap143Old.x nativeGap143Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_142_Gen, nativeHeatStep_hInd_142_Gen]

theorem nativeHeatStepFrameNum_142_Gen : NativeHeatStepFrameNum 142 := by
  have h1 := nativeHeatStep_hOld_142_Gen
  have h2 := nativeHeatStep_hInd_142_Gen
  have h3 := nativeHeatStep_hVar_142_Gen
  have h4 := nativeHeatStep_hQm_142_Gen
  have h5 := nativeHeatStep_hQN_142_Gen
  have h6 := nativeHeatStep_hY0_142_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_142_Gen : NativeHeatStepIndivNum 142 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 142 (by norm_num)) = nativeGap143Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_142_Gen]; exact nativeGap143Old_source
  · rw [hc, nativeHeatStep_hInd_142_Gen]; exact nativeGap143Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_142_Gen : nativeHeatY48Gen 142 = nativeHeat142Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_142_Gen, nativeHeatStep_hFr_142_Gen,
    nativeHeatStep_hCoef_142_Gen, nativeHeatStep_hFixed_142_Gen,
    nativeHeatStep_hBase_142_Gen]
  exact nativeHeat142All48

theorem nativeHeatResultGen_142 : nativeHeatResultGen 142 = nativeHeat142Result := by
  rw [← nativeHeat142Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_142_Gen, nativeHeatStep_hY0_142_Gen, nativeHeatStep_hExp_142_Gen,
    nativeHeatStep_hInit_142_Gen, nativeHeatStep_hFixed_142_Gen]

end ASDExplicitGamma.Native

end
