module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat085Complete
public import ASDExplicitGamma.Numerics.Native.Gap086Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_085_Gen : nativeHeatOldRowGen 85 = nativeGap086Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_085_Gen : nativeHeatIndividualGen 85 = nativeGap086Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_085_Gen : nativeHeatGenVariance 85 = nativeHeat085Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_085_Gen, nativeHeat085Variance_formula]

theorem nativeHeatStep_hSpec_085_Gen : nativeHeatGenSpectral 85 = nativeHeat085Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_085_Gen, nativeHeat085Variance_formula]

theorem nativeHeatStep_hQm_085_Gen : nativeHeatGenQm 85 = nativeHeat085Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_085_Gen, nativeHeatStep_hSpec_085_Gen,
    nativeHeat085Qm_formula]

theorem nativeHeatStep_hQN_085_Gen : nativeHeatQNGen 85 = nativeHeat085QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_085_Gen, nativeHeat085QN_formula]

theorem nativeHeatStep_hFr_085_Gen : nativeHeatFramesGen 85 = nativeHeat085Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_085_Gen, nativeHeatStep_hInd_085_Gen,
    nativeHeatStep_hVar_085_Gen, nativeHeatStep_hQN_085_Gen, nativeHeat085Frames_formula]

theorem nativeHeatStep_hArg_085_Gen : nativeHeatExpArgGen 85 = nativeHeatExpArg nativeGap086Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_085_Gen]

theorem nativeHeatStep_hExp_085_Gen : nativeHeatExpGen 85 = nativeHeat085Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_085_Gen, nativeHeat085Exp_formula]

theorem nativeHeatStep_hCoef_085_Gen : nativeHeatCoefGen 85 = nativeHeat085Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_085_Gen, nativeHeat085Coef_formula]

theorem nativeHeatStep_hInit_085_Gen : nativeHeatInitGen 85 = nativeHeat085Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_085_Gen, nativeHeatStep_hVar_085_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat085Init00_formula
    · exact nativeHeat085Init01_formula
    · exact nativeHeat085Init02_formula
    · exact nativeHeat085Init03_formula
    · exact nativeHeat085Init04_formula
    · exact nativeHeat085Init05_formula
    · exact nativeHeat085Init06_formula
    · exact nativeHeat085Init07_formula
    · exact nativeHeat085Init08_formula
    · exact nativeHeat085Init09_formula
    · exact nativeHeat085Init10_formula
    · exact nativeHeat085Init11_formula
    · exact nativeHeat085Init12_formula
    · exact nativeHeat085Init13_formula
    · exact nativeHeat085Init14_formula
    · exact nativeHeat085Init15_formula
    · exact nativeHeat085Init16_formula
    · exact nativeHeat085Init17_formula
    · exact nativeHeat085Init18_formula
    · exact nativeHeat085Init19_formula
    · exact nativeHeat085Init20_formula
theorem nativeHeatStep_hBase_085_Gen : nativeHeatBaseGen 85 = nativeHeat085Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_085_Gen, nativeHeatStep_hInit_085_Gen, nativeHeat085Base_formula]

theorem nativeHeatStep_hFixed_085_Gen : nativeHeatFixedGen 85 = nativeHeat085Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_085_Gen, nativeHeatStep_hFr_085_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat085Fixed01_formula
    · exact nativeHeat085Fixed02_formula
    · exact nativeHeat085Fixed03_formula
    · exact nativeHeat085Fixed04_formula
    · exact nativeHeat085Fixed05_formula
    · exact nativeHeat085Fixed06_formula
    · exact nativeHeat085Fixed07_formula
    · exact nativeHeat085Fixed08_formula
    · exact nativeHeat085Fixed09_formula
    · exact nativeHeat085Fixed10_formula
    · exact nativeHeat085Fixed11_formula
    · exact nativeHeat085Fixed12_formula
    · exact nativeHeat085Fixed13_formula
    · exact nativeHeat085Fixed14_formula
    · exact nativeHeat085Fixed15_formula
    · exact nativeHeat085Fixed16_formula
    · exact nativeHeat085Fixed17_formula
    · exact nativeHeat085Fixed18_formula
    · exact nativeHeat085Fixed19_formula
    · exact nativeHeat085Fixed20_formula

theorem nativeHeatStep_chk_085_Gen :
    nativeHeatPassRootsOk nativeGap086Old nativeHeat085Frames nativeHeat085Coef nativeHeat085Fixed nativeHeat085Base 48 nativeHeat085Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_085_Gen : NativeHeatStepPassNum 85 := by
  refine nativeHeatStepPassNum_of_literals 85 nativeGap086Old nativeHeat085Frames (nativeHeatExpArg nativeGap086Old)
    nativeHeat085Exp nativeHeat085Coef nativeHeat085Fixed nativeHeat085Init nativeHeat085Base nativeHeatStep_hOld_085_Gen
    nativeHeatStep_hFr_085_Gen nativeHeatStep_hArg_085_Gen nativeHeatStep_hExp_085_Gen
    nativeHeatStep_hCoef_085_Gen nativeHeatStep_hFixed_085_Gen
    nativeHeatStep_hInit_085_Gen nativeHeatStep_hBase_085_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_085_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_085_Gen :
    nativeHeatY0Gen 85 = nativeShiftedFrame 1 (min nativeGap086Old.x nativeGap086Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_085_Gen, nativeHeatStep_hInd_085_Gen]

theorem nativeHeatStepFrameNum_085_Gen : NativeHeatStepFrameNum 85 := by
  have h1 := nativeHeatStep_hOld_085_Gen
  have h2 := nativeHeatStep_hInd_085_Gen
  have h3 := nativeHeatStep_hVar_085_Gen
  have h4 := nativeHeatStep_hQm_085_Gen
  have h5 := nativeHeatStep_hQN_085_Gen
  have h6 := nativeHeatStep_hY0_085_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_085_Gen : NativeHeatStepIndivNum 85 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 85 (by norm_num)) = nativeGap086Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_085_Gen]; exact nativeGap086Old_source
  · rw [hc, nativeHeatStep_hInd_085_Gen]; exact nativeGap086Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_085_Gen : nativeHeatY48Gen 85 = nativeHeat085Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_085_Gen, nativeHeatStep_hFr_085_Gen,
    nativeHeatStep_hCoef_085_Gen, nativeHeatStep_hFixed_085_Gen,
    nativeHeatStep_hBase_085_Gen]
  exact nativeHeat085All48

theorem nativeHeatResultGen_085 : nativeHeatResultGen 85 = nativeHeat085Result := by
  rw [← nativeHeat085Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_085_Gen, nativeHeatStep_hY0_085_Gen, nativeHeatStep_hExp_085_Gen,
    nativeHeatStep_hInit_085_Gen, nativeHeatStep_hFixed_085_Gen]

end ASDExplicitGamma.Native

end
