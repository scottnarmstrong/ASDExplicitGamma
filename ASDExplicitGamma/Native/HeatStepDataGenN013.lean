module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat013Complete
public import ASDExplicitGamma.Numerics.Native.Gap014Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_013_Gen : nativeHeatOldRowGen 13 = nativeGap014Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_013_Gen : nativeHeatIndividualGen 13 = nativeGap014Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_013_Gen : nativeHeatGenVariance 13 = nativeHeat013Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_013_Gen, nativeHeat013Variance_formula]

theorem nativeHeatStep_hSpec_013_Gen : nativeHeatGenSpectral 13 = nativeHeat013Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_013_Gen, nativeHeat013Variance_formula]

theorem nativeHeatStep_hQm_013_Gen : nativeHeatGenQm 13 = nativeHeat013Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_013_Gen, nativeHeatStep_hSpec_013_Gen,
    nativeHeat013Qm_formula]

theorem nativeHeatStep_hQN_013_Gen : nativeHeatQNGen 13 = nativeHeat013QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_013_Gen, nativeHeat013QN_formula]

theorem nativeHeatStep_hFr_013_Gen : nativeHeatFramesGen 13 = nativeHeat013Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_013_Gen, nativeHeatStep_hInd_013_Gen,
    nativeHeatStep_hVar_013_Gen, nativeHeatStep_hQN_013_Gen, nativeHeat013Frames_formula]

theorem nativeHeatStep_hArg_013_Gen : nativeHeatExpArgGen 13 = nativeHeatExpArg nativeGap014Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_013_Gen]

theorem nativeHeatStep_hExp_013_Gen : nativeHeatExpGen 13 = nativeHeat013Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_013_Gen, nativeHeat013Exp_formula]

theorem nativeHeatStep_hCoef_013_Gen : nativeHeatCoefGen 13 = nativeHeat013Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_013_Gen, nativeHeat013Coef_formula]

theorem nativeHeatStep_hInit_013_Gen : nativeHeatInitGen 13 = nativeHeat013Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_013_Gen, nativeHeatStep_hVar_013_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat013Init00_formula
    · exact nativeHeat013Init01_formula
    · exact nativeHeat013Init02_formula
    · exact nativeHeat013Init03_formula
    · exact nativeHeat013Init04_formula
    · exact nativeHeat013Init05_formula
    · exact nativeHeat013Init06_formula
    · exact nativeHeat013Init07_formula
    · exact nativeHeat013Init08_formula
    · exact nativeHeat013Init09_formula
    · exact nativeHeat013Init10_formula
    · exact nativeHeat013Init11_formula
    · exact nativeHeat013Init12_formula
    · exact nativeHeat013Init13_formula
    · exact nativeHeat013Init14_formula
    · exact nativeHeat013Init15_formula
    · exact nativeHeat013Init16_formula
    · exact nativeHeat013Init17_formula
    · exact nativeHeat013Init18_formula
    · exact nativeHeat013Init19_formula
    · exact nativeHeat013Init20_formula
theorem nativeHeatStep_hBase_013_Gen : nativeHeatBaseGen 13 = nativeHeat013Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_013_Gen, nativeHeatStep_hInit_013_Gen, nativeHeat013Base_formula]

theorem nativeHeatStep_hFixed_013_Gen : nativeHeatFixedGen 13 = nativeHeat013Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_013_Gen, nativeHeatStep_hFr_013_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat013Fixed01_formula
    · exact nativeHeat013Fixed02_formula
    · exact nativeHeat013Fixed03_formula
    · exact nativeHeat013Fixed04_formula
    · exact nativeHeat013Fixed05_formula
    · exact nativeHeat013Fixed06_formula
    · exact nativeHeat013Fixed07_formula
    · exact nativeHeat013Fixed08_formula
    · exact nativeHeat013Fixed09_formula
    · exact nativeHeat013Fixed10_formula
    · exact nativeHeat013Fixed11_formula
    · exact nativeHeat013Fixed12_formula
    · exact nativeHeat013Fixed13_formula
    · exact nativeHeat013Fixed14_formula
    · exact nativeHeat013Fixed15_formula
    · exact nativeHeat013Fixed16_formula
    · exact nativeHeat013Fixed17_formula
    · exact nativeHeat013Fixed18_formula
    · exact nativeHeat013Fixed19_formula
    · exact nativeHeat013Fixed20_formula

theorem nativeHeatStep_chk_013_Gen :
    nativeHeatPassRootsOk nativeGap014Old nativeHeat013Frames nativeHeat013Coef nativeHeat013Fixed nativeHeat013Base 48 nativeHeat013Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_013_Gen : NativeHeatStepPassNum 13 := by
  refine nativeHeatStepPassNum_of_literals 13 nativeGap014Old nativeHeat013Frames (nativeHeatExpArg nativeGap014Old)
    nativeHeat013Exp nativeHeat013Coef nativeHeat013Fixed nativeHeat013Init nativeHeat013Base nativeHeatStep_hOld_013_Gen
    nativeHeatStep_hFr_013_Gen nativeHeatStep_hArg_013_Gen nativeHeatStep_hExp_013_Gen
    nativeHeatStep_hCoef_013_Gen nativeHeatStep_hFixed_013_Gen
    nativeHeatStep_hInit_013_Gen nativeHeatStep_hBase_013_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_013_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_013_Gen :
    nativeHeatY0Gen 13 = nativeShiftedFrame 1 (min nativeGap014Old.x nativeGap014Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_013_Gen, nativeHeatStep_hInd_013_Gen]

theorem nativeHeatStepFrameNum_013_Gen : NativeHeatStepFrameNum 13 := by
  have h1 := nativeHeatStep_hOld_013_Gen
  have h2 := nativeHeatStep_hInd_013_Gen
  have h3 := nativeHeatStep_hVar_013_Gen
  have h4 := nativeHeatStep_hQm_013_Gen
  have h5 := nativeHeatStep_hQN_013_Gen
  have h6 := nativeHeatStep_hY0_013_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_013_Gen : NativeHeatStepIndivNum 13 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 13 (by norm_num)) = nativeGap014Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_013_Gen]; exact nativeGap014Old_source
  · rw [hc, nativeHeatStep_hInd_013_Gen]; exact nativeGap014Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_013_Gen : nativeHeatY48Gen 13 = nativeHeat013Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_013_Gen, nativeHeatStep_hFr_013_Gen,
    nativeHeatStep_hCoef_013_Gen, nativeHeatStep_hFixed_013_Gen,
    nativeHeatStep_hBase_013_Gen]
  exact nativeHeat013All48

theorem nativeHeatResultGen_013 : nativeHeatResultGen 13 = nativeHeat013Result := by
  rw [← nativeHeat013Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_013_Gen, nativeHeatStep_hY0_013_Gen, nativeHeatStep_hExp_013_Gen,
    nativeHeatStep_hInit_013_Gen, nativeHeatStep_hFixed_013_Gen]

end ASDExplicitGamma.Native

end
