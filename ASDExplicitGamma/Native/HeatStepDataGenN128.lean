module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat128Complete
public import ASDExplicitGamma.Numerics.Native.Gap129Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_128_Gen : nativeHeatOldRowGen 128 = nativeGap129Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_128_Gen : nativeHeatIndividualGen 128 = nativeGap129Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_128_Gen : nativeHeatGenVariance 128 = nativeHeat128Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_128_Gen, nativeHeat128Variance_formula]

theorem nativeHeatStep_hSpec_128_Gen : nativeHeatGenSpectral 128 = nativeHeat128Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_128_Gen, nativeHeat128Variance_formula]

theorem nativeHeatStep_hQm_128_Gen : nativeHeatGenQm 128 = nativeHeat128Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_128_Gen, nativeHeatStep_hSpec_128_Gen,
    nativeHeat128Qm_formula]

theorem nativeHeatStep_hQN_128_Gen : nativeHeatQNGen 128 = nativeHeat128QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_128_Gen, nativeHeat128QN_formula]

theorem nativeHeatStep_hFr_128_Gen : nativeHeatFramesGen 128 = nativeHeat128Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_128_Gen, nativeHeatStep_hInd_128_Gen,
    nativeHeatStep_hVar_128_Gen, nativeHeatStep_hQN_128_Gen, nativeHeat128Frames_formula]

theorem nativeHeatStep_hArg_128_Gen : nativeHeatExpArgGen 128 = nativeHeatExpArg nativeGap129Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_128_Gen]

theorem nativeHeatStep_hExp_128_Gen : nativeHeatExpGen 128 = nativeHeat128Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_128_Gen, nativeHeat128Exp_formula]

theorem nativeHeatStep_hCoef_128_Gen : nativeHeatCoefGen 128 = nativeHeat128Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_128_Gen, nativeHeat128Coef_formula]

theorem nativeHeatStep_hInit_128_Gen : nativeHeatInitGen 128 = nativeHeat128Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_128_Gen, nativeHeatStep_hVar_128_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat128Init00_formula
    · exact nativeHeat128Init01_formula
    · exact nativeHeat128Init02_formula
    · exact nativeHeat128Init03_formula
    · exact nativeHeat128Init04_formula
    · exact nativeHeat128Init05_formula
    · exact nativeHeat128Init06_formula
    · exact nativeHeat128Init07_formula
    · exact nativeHeat128Init08_formula
    · exact nativeHeat128Init09_formula
    · exact nativeHeat128Init10_formula
    · exact nativeHeat128Init11_formula
    · exact nativeHeat128Init12_formula
    · exact nativeHeat128Init13_formula
    · exact nativeHeat128Init14_formula
    · exact nativeHeat128Init15_formula
    · exact nativeHeat128Init16_formula
    · exact nativeHeat128Init17_formula
    · exact nativeHeat128Init18_formula
    · exact nativeHeat128Init19_formula
    · exact nativeHeat128Init20_formula
theorem nativeHeatStep_hBase_128_Gen : nativeHeatBaseGen 128 = nativeHeat128Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_128_Gen, nativeHeatStep_hInit_128_Gen, nativeHeat128Base_formula]

theorem nativeHeatStep_hFixed_128_Gen : nativeHeatFixedGen 128 = nativeHeat128Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_128_Gen, nativeHeatStep_hFr_128_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat128Fixed01_formula
    · exact nativeHeat128Fixed02_formula
    · exact nativeHeat128Fixed03_formula
    · exact nativeHeat128Fixed04_formula
    · exact nativeHeat128Fixed05_formula
    · exact nativeHeat128Fixed06_formula
    · exact nativeHeat128Fixed07_formula
    · exact nativeHeat128Fixed08_formula
    · exact nativeHeat128Fixed09_formula
    · exact nativeHeat128Fixed10_formula
    · exact nativeHeat128Fixed11_formula
    · exact nativeHeat128Fixed12_formula
    · exact nativeHeat128Fixed13_formula
    · exact nativeHeat128Fixed14_formula
    · exact nativeHeat128Fixed15_formula
    · exact nativeHeat128Fixed16_formula
    · exact nativeHeat128Fixed17_formula
    · exact nativeHeat128Fixed18_formula
    · exact nativeHeat128Fixed19_formula
    · exact nativeHeat128Fixed20_formula

theorem nativeHeatStep_chk_128_Gen :
    nativeHeatPassRootsOk nativeGap129Old nativeHeat128Frames nativeHeat128Coef nativeHeat128Fixed nativeHeat128Base 48 nativeHeat128Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_128_Gen : NativeHeatStepPassNum 128 := by
  refine nativeHeatStepPassNum_of_literals 128 nativeGap129Old nativeHeat128Frames (nativeHeatExpArg nativeGap129Old)
    nativeHeat128Exp nativeHeat128Coef nativeHeat128Fixed nativeHeat128Init nativeHeat128Base nativeHeatStep_hOld_128_Gen
    nativeHeatStep_hFr_128_Gen nativeHeatStep_hArg_128_Gen nativeHeatStep_hExp_128_Gen
    nativeHeatStep_hCoef_128_Gen nativeHeatStep_hFixed_128_Gen
    nativeHeatStep_hInit_128_Gen nativeHeatStep_hBase_128_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_128_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_128_Gen :
    nativeHeatY0Gen 128 = nativeShiftedFrame 1 (min nativeGap129Old.x nativeGap129Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_128_Gen, nativeHeatStep_hInd_128_Gen]

theorem nativeHeatStepFrameNum_128_Gen : NativeHeatStepFrameNum 128 := by
  have h1 := nativeHeatStep_hOld_128_Gen
  have h2 := nativeHeatStep_hInd_128_Gen
  have h3 := nativeHeatStep_hVar_128_Gen
  have h4 := nativeHeatStep_hQm_128_Gen
  have h5 := nativeHeatStep_hQN_128_Gen
  have h6 := nativeHeatStep_hY0_128_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_128_Gen : NativeHeatStepIndivNum 128 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 128 (by norm_num)) = nativeGap129Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_128_Gen]; exact nativeGap129Old_source
  · rw [hc, nativeHeatStep_hInd_128_Gen]; exact nativeGap129Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_128_Gen : nativeHeatY48Gen 128 = nativeHeat128Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_128_Gen, nativeHeatStep_hFr_128_Gen,
    nativeHeatStep_hCoef_128_Gen, nativeHeatStep_hFixed_128_Gen,
    nativeHeatStep_hBase_128_Gen]
  exact nativeHeat128All48

theorem nativeHeatResultGen_128 : nativeHeatResultGen 128 = nativeHeat128Result := by
  rw [← nativeHeat128Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_128_Gen, nativeHeatStep_hY0_128_Gen, nativeHeatStep_hExp_128_Gen,
    nativeHeatStep_hInit_128_Gen, nativeHeatStep_hFixed_128_Gen]

end ASDExplicitGamma.Native

end
