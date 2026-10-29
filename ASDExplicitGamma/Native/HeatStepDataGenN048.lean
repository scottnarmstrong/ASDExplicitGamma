module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat048Complete
public import ASDExplicitGamma.Numerics.Native.Gap049Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_048_Gen : nativeHeatOldRowGen 48 = nativeGap049Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_048_Gen : nativeHeatIndividualGen 48 = nativeGap049Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_048_Gen : nativeHeatGenVariance 48 = nativeHeat048Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_048_Gen, nativeHeat048Variance_formula]

theorem nativeHeatStep_hSpec_048_Gen : nativeHeatGenSpectral 48 = nativeHeat048Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_048_Gen, nativeHeat048Variance_formula]

theorem nativeHeatStep_hQm_048_Gen : nativeHeatGenQm 48 = nativeHeat048Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_048_Gen, nativeHeatStep_hSpec_048_Gen,
    nativeHeat048Qm_formula]

theorem nativeHeatStep_hQN_048_Gen : nativeHeatQNGen 48 = nativeHeat048QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_048_Gen, nativeHeat048QN_formula]

theorem nativeHeatStep_hFr_048_Gen : nativeHeatFramesGen 48 = nativeHeat048Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_048_Gen, nativeHeatStep_hInd_048_Gen,
    nativeHeatStep_hVar_048_Gen, nativeHeatStep_hQN_048_Gen, nativeHeat048Frames_formula]

theorem nativeHeatStep_hArg_048_Gen : nativeHeatExpArgGen 48 = nativeHeatExpArg nativeGap049Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_048_Gen]

theorem nativeHeatStep_hExp_048_Gen : nativeHeatExpGen 48 = nativeHeat048Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_048_Gen, nativeHeat048Exp_formula]

theorem nativeHeatStep_hCoef_048_Gen : nativeHeatCoefGen 48 = nativeHeat048Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_048_Gen, nativeHeat048Coef_formula]

theorem nativeHeatStep_hInit_048_Gen : nativeHeatInitGen 48 = nativeHeat048Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_048_Gen, nativeHeatStep_hVar_048_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat048Init00_formula
    · exact nativeHeat048Init01_formula
    · exact nativeHeat048Init02_formula
    · exact nativeHeat048Init03_formula
    · exact nativeHeat048Init04_formula
    · exact nativeHeat048Init05_formula
    · exact nativeHeat048Init06_formula
    · exact nativeHeat048Init07_formula
    · exact nativeHeat048Init08_formula
    · exact nativeHeat048Init09_formula
    · exact nativeHeat048Init10_formula
    · exact nativeHeat048Init11_formula
    · exact nativeHeat048Init12_formula
    · exact nativeHeat048Init13_formula
    · exact nativeHeat048Init14_formula
    · exact nativeHeat048Init15_formula
    · exact nativeHeat048Init16_formula
    · exact nativeHeat048Init17_formula
    · exact nativeHeat048Init18_formula
    · exact nativeHeat048Init19_formula
    · exact nativeHeat048Init20_formula
theorem nativeHeatStep_hBase_048_Gen : nativeHeatBaseGen 48 = nativeHeat048Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_048_Gen, nativeHeatStep_hInit_048_Gen, nativeHeat048Base_formula]

theorem nativeHeatStep_hFixed_048_Gen : nativeHeatFixedGen 48 = nativeHeat048Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_048_Gen, nativeHeatStep_hFr_048_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat048Fixed01_formula
    · exact nativeHeat048Fixed02_formula
    · exact nativeHeat048Fixed03_formula
    · exact nativeHeat048Fixed04_formula
    · exact nativeHeat048Fixed05_formula
    · exact nativeHeat048Fixed06_formula
    · exact nativeHeat048Fixed07_formula
    · exact nativeHeat048Fixed08_formula
    · exact nativeHeat048Fixed09_formula
    · exact nativeHeat048Fixed10_formula
    · exact nativeHeat048Fixed11_formula
    · exact nativeHeat048Fixed12_formula
    · exact nativeHeat048Fixed13_formula
    · exact nativeHeat048Fixed14_formula
    · exact nativeHeat048Fixed15_formula
    · exact nativeHeat048Fixed16_formula
    · exact nativeHeat048Fixed17_formula
    · exact nativeHeat048Fixed18_formula
    · exact nativeHeat048Fixed19_formula
    · exact nativeHeat048Fixed20_formula

theorem nativeHeatStep_chk_048_Gen :
    nativeHeatPassRootsOk nativeGap049Old nativeHeat048Frames nativeHeat048Coef nativeHeat048Fixed nativeHeat048Base 48 nativeHeat048Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_048_Gen : NativeHeatStepPassNum 48 := by
  refine nativeHeatStepPassNum_of_literals 48 nativeGap049Old nativeHeat048Frames (nativeHeatExpArg nativeGap049Old)
    nativeHeat048Exp nativeHeat048Coef nativeHeat048Fixed nativeHeat048Init nativeHeat048Base nativeHeatStep_hOld_048_Gen
    nativeHeatStep_hFr_048_Gen nativeHeatStep_hArg_048_Gen nativeHeatStep_hExp_048_Gen
    nativeHeatStep_hCoef_048_Gen nativeHeatStep_hFixed_048_Gen
    nativeHeatStep_hInit_048_Gen nativeHeatStep_hBase_048_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_048_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_048_Gen :
    nativeHeatY0Gen 48 = nativeShiftedFrame 1 (min nativeGap049Old.x nativeGap049Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_048_Gen, nativeHeatStep_hInd_048_Gen]

theorem nativeHeatStepFrameNum_048_Gen : NativeHeatStepFrameNum 48 := by
  have h1 := nativeHeatStep_hOld_048_Gen
  have h2 := nativeHeatStep_hInd_048_Gen
  have h3 := nativeHeatStep_hVar_048_Gen
  have h4 := nativeHeatStep_hQm_048_Gen
  have h5 := nativeHeatStep_hQN_048_Gen
  have h6 := nativeHeatStep_hY0_048_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_048_Gen : NativeHeatStepIndivNum 48 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 48 (by norm_num)) = nativeGap049Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_048_Gen]; exact nativeGap049Old_source
  · rw [hc, nativeHeatStep_hInd_048_Gen]; exact nativeGap049Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_048_Gen : nativeHeatY48Gen 48 = nativeHeat048Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_048_Gen, nativeHeatStep_hFr_048_Gen,
    nativeHeatStep_hCoef_048_Gen, nativeHeatStep_hFixed_048_Gen,
    nativeHeatStep_hBase_048_Gen]
  exact nativeHeat048All48

theorem nativeHeatResultGen_048 : nativeHeatResultGen 48 = nativeHeat048Result := by
  rw [← nativeHeat048Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_048_Gen, nativeHeatStep_hY0_048_Gen, nativeHeatStep_hExp_048_Gen,
    nativeHeatStep_hInit_048_Gen, nativeHeatStep_hFixed_048_Gen]

end ASDExplicitGamma.Native

end
