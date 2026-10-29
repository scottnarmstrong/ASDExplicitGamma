module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat027Complete
public import ASDExplicitGamma.Numerics.Native.Gap028Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_027_Gen : nativeHeatOldRowGen 27 = nativeGap028Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_027_Gen : nativeHeatIndividualGen 27 = nativeGap028Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_027_Gen : nativeHeatGenVariance 27 = nativeHeat027Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_027_Gen, nativeHeat027Variance_formula]

theorem nativeHeatStep_hSpec_027_Gen : nativeHeatGenSpectral 27 = nativeHeat027Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_027_Gen, nativeHeat027Variance_formula]

theorem nativeHeatStep_hQm_027_Gen : nativeHeatGenQm 27 = nativeHeat027Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_027_Gen, nativeHeatStep_hSpec_027_Gen,
    nativeHeat027Qm_formula]

theorem nativeHeatStep_hQN_027_Gen : nativeHeatQNGen 27 = nativeHeat027QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_027_Gen, nativeHeat027QN_formula]

theorem nativeHeatStep_hFr_027_Gen : nativeHeatFramesGen 27 = nativeHeat027Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_027_Gen, nativeHeatStep_hInd_027_Gen,
    nativeHeatStep_hVar_027_Gen, nativeHeatStep_hQN_027_Gen, nativeHeat027Frames_formula]

theorem nativeHeatStep_hArg_027_Gen : nativeHeatExpArgGen 27 = nativeHeatExpArg nativeGap028Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_027_Gen]

theorem nativeHeatStep_hExp_027_Gen : nativeHeatExpGen 27 = nativeHeat027Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_027_Gen, nativeHeat027Exp_formula]

theorem nativeHeatStep_hCoef_027_Gen : nativeHeatCoefGen 27 = nativeHeat027Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_027_Gen, nativeHeat027Coef_formula]

theorem nativeHeatStep_hInit_027_Gen : nativeHeatInitGen 27 = nativeHeat027Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_027_Gen, nativeHeatStep_hVar_027_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat027Init00_formula
    · exact nativeHeat027Init01_formula
    · exact nativeHeat027Init02_formula
    · exact nativeHeat027Init03_formula
    · exact nativeHeat027Init04_formula
    · exact nativeHeat027Init05_formula
    · exact nativeHeat027Init06_formula
    · exact nativeHeat027Init07_formula
    · exact nativeHeat027Init08_formula
    · exact nativeHeat027Init09_formula
    · exact nativeHeat027Init10_formula
    · exact nativeHeat027Init11_formula
    · exact nativeHeat027Init12_formula
    · exact nativeHeat027Init13_formula
    · exact nativeHeat027Init14_formula
    · exact nativeHeat027Init15_formula
    · exact nativeHeat027Init16_formula
    · exact nativeHeat027Init17_formula
    · exact nativeHeat027Init18_formula
    · exact nativeHeat027Init19_formula
    · exact nativeHeat027Init20_formula
theorem nativeHeatStep_hBase_027_Gen : nativeHeatBaseGen 27 = nativeHeat027Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_027_Gen, nativeHeatStep_hInit_027_Gen, nativeHeat027Base_formula]

theorem nativeHeatStep_hFixed_027_Gen : nativeHeatFixedGen 27 = nativeHeat027Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_027_Gen, nativeHeatStep_hFr_027_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat027Fixed01_formula
    · exact nativeHeat027Fixed02_formula
    · exact nativeHeat027Fixed03_formula
    · exact nativeHeat027Fixed04_formula
    · exact nativeHeat027Fixed05_formula
    · exact nativeHeat027Fixed06_formula
    · exact nativeHeat027Fixed07_formula
    · exact nativeHeat027Fixed08_formula
    · exact nativeHeat027Fixed09_formula
    · exact nativeHeat027Fixed10_formula
    · exact nativeHeat027Fixed11_formula
    · exact nativeHeat027Fixed12_formula
    · exact nativeHeat027Fixed13_formula
    · exact nativeHeat027Fixed14_formula
    · exact nativeHeat027Fixed15_formula
    · exact nativeHeat027Fixed16_formula
    · exact nativeHeat027Fixed17_formula
    · exact nativeHeat027Fixed18_formula
    · exact nativeHeat027Fixed19_formula
    · exact nativeHeat027Fixed20_formula

theorem nativeHeatStep_chk_027_Gen :
    nativeHeatPassRootsOk nativeGap028Old nativeHeat027Frames nativeHeat027Coef nativeHeat027Fixed nativeHeat027Base 48 nativeHeat027Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_027_Gen : NativeHeatStepPassNum 27 := by
  refine nativeHeatStepPassNum_of_literals 27 nativeGap028Old nativeHeat027Frames (nativeHeatExpArg nativeGap028Old)
    nativeHeat027Exp nativeHeat027Coef nativeHeat027Fixed nativeHeat027Init nativeHeat027Base nativeHeatStep_hOld_027_Gen
    nativeHeatStep_hFr_027_Gen nativeHeatStep_hArg_027_Gen nativeHeatStep_hExp_027_Gen
    nativeHeatStep_hCoef_027_Gen nativeHeatStep_hFixed_027_Gen
    nativeHeatStep_hInit_027_Gen nativeHeatStep_hBase_027_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_027_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_027_Gen :
    nativeHeatY0Gen 27 = nativeShiftedFrame 1 (min nativeGap028Old.x nativeGap028Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_027_Gen, nativeHeatStep_hInd_027_Gen]

theorem nativeHeatStepFrameNum_027_Gen : NativeHeatStepFrameNum 27 := by
  have h1 := nativeHeatStep_hOld_027_Gen
  have h2 := nativeHeatStep_hInd_027_Gen
  have h3 := nativeHeatStep_hVar_027_Gen
  have h4 := nativeHeatStep_hQm_027_Gen
  have h5 := nativeHeatStep_hQN_027_Gen
  have h6 := nativeHeatStep_hY0_027_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_027_Gen : NativeHeatStepIndivNum 27 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 27 (by norm_num)) = nativeGap028Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_027_Gen]; exact nativeGap028Old_source
  · rw [hc, nativeHeatStep_hInd_027_Gen]; exact nativeGap028Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_027_Gen : nativeHeatY48Gen 27 = nativeHeat027Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_027_Gen, nativeHeatStep_hFr_027_Gen,
    nativeHeatStep_hCoef_027_Gen, nativeHeatStep_hFixed_027_Gen,
    nativeHeatStep_hBase_027_Gen]
  exact nativeHeat027All48

theorem nativeHeatResultGen_027 : nativeHeatResultGen 27 = nativeHeat027Result := by
  rw [← nativeHeat027Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_027_Gen, nativeHeatStep_hY0_027_Gen, nativeHeatStep_hExp_027_Gen,
    nativeHeatStep_hInit_027_Gen, nativeHeatStep_hFixed_027_Gen]

end ASDExplicitGamma.Native

end
