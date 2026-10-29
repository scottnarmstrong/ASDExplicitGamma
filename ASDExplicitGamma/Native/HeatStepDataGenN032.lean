module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat032Complete
public import ASDExplicitGamma.Numerics.Native.Gap033Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_032_Gen : nativeHeatOldRowGen 32 = nativeGap033Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_032_Gen : nativeHeatIndividualGen 32 = nativeGap033Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_032_Gen : nativeHeatGenVariance 32 = nativeHeat032Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_032_Gen, nativeHeat032Variance_formula]

theorem nativeHeatStep_hSpec_032_Gen : nativeHeatGenSpectral 32 = nativeHeat032Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_032_Gen, nativeHeat032Variance_formula]

theorem nativeHeatStep_hQm_032_Gen : nativeHeatGenQm 32 = nativeHeat032Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_032_Gen, nativeHeatStep_hSpec_032_Gen,
    nativeHeat032Qm_formula]

theorem nativeHeatStep_hQN_032_Gen : nativeHeatQNGen 32 = nativeHeat032QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_032_Gen, nativeHeat032QN_formula]

theorem nativeHeatStep_hFr_032_Gen : nativeHeatFramesGen 32 = nativeHeat032Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_032_Gen, nativeHeatStep_hInd_032_Gen,
    nativeHeatStep_hVar_032_Gen, nativeHeatStep_hQN_032_Gen, nativeHeat032Frames_formula]

theorem nativeHeatStep_hArg_032_Gen : nativeHeatExpArgGen 32 = nativeHeatExpArg nativeGap033Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_032_Gen]

theorem nativeHeatStep_hExp_032_Gen : nativeHeatExpGen 32 = nativeHeat032Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_032_Gen, nativeHeat032Exp_formula]

theorem nativeHeatStep_hCoef_032_Gen : nativeHeatCoefGen 32 = nativeHeat032Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_032_Gen, nativeHeat032Coef_formula]

theorem nativeHeatStep_hInit_032_Gen : nativeHeatInitGen 32 = nativeHeat032Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_032_Gen, nativeHeatStep_hVar_032_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat032Init00_formula
    · exact nativeHeat032Init01_formula
    · exact nativeHeat032Init02_formula
    · exact nativeHeat032Init03_formula
    · exact nativeHeat032Init04_formula
    · exact nativeHeat032Init05_formula
    · exact nativeHeat032Init06_formula
    · exact nativeHeat032Init07_formula
    · exact nativeHeat032Init08_formula
    · exact nativeHeat032Init09_formula
    · exact nativeHeat032Init10_formula
    · exact nativeHeat032Init11_formula
    · exact nativeHeat032Init12_formula
    · exact nativeHeat032Init13_formula
    · exact nativeHeat032Init14_formula
    · exact nativeHeat032Init15_formula
    · exact nativeHeat032Init16_formula
    · exact nativeHeat032Init17_formula
    · exact nativeHeat032Init18_formula
    · exact nativeHeat032Init19_formula
    · exact nativeHeat032Init20_formula
theorem nativeHeatStep_hBase_032_Gen : nativeHeatBaseGen 32 = nativeHeat032Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_032_Gen, nativeHeatStep_hInit_032_Gen, nativeHeat032Base_formula]

theorem nativeHeatStep_hFixed_032_Gen : nativeHeatFixedGen 32 = nativeHeat032Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_032_Gen, nativeHeatStep_hFr_032_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat032Fixed01_formula
    · exact nativeHeat032Fixed02_formula
    · exact nativeHeat032Fixed03_formula
    · exact nativeHeat032Fixed04_formula
    · exact nativeHeat032Fixed05_formula
    · exact nativeHeat032Fixed06_formula
    · exact nativeHeat032Fixed07_formula
    · exact nativeHeat032Fixed08_formula
    · exact nativeHeat032Fixed09_formula
    · exact nativeHeat032Fixed10_formula
    · exact nativeHeat032Fixed11_formula
    · exact nativeHeat032Fixed12_formula
    · exact nativeHeat032Fixed13_formula
    · exact nativeHeat032Fixed14_formula
    · exact nativeHeat032Fixed15_formula
    · exact nativeHeat032Fixed16_formula
    · exact nativeHeat032Fixed17_formula
    · exact nativeHeat032Fixed18_formula
    · exact nativeHeat032Fixed19_formula
    · exact nativeHeat032Fixed20_formula

theorem nativeHeatStep_chk_032_Gen :
    nativeHeatPassRootsOk nativeGap033Old nativeHeat032Frames nativeHeat032Coef nativeHeat032Fixed nativeHeat032Base 48 nativeHeat032Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_032_Gen : NativeHeatStepPassNum 32 := by
  refine nativeHeatStepPassNum_of_literals 32 nativeGap033Old nativeHeat032Frames (nativeHeatExpArg nativeGap033Old)
    nativeHeat032Exp nativeHeat032Coef nativeHeat032Fixed nativeHeat032Init nativeHeat032Base nativeHeatStep_hOld_032_Gen
    nativeHeatStep_hFr_032_Gen nativeHeatStep_hArg_032_Gen nativeHeatStep_hExp_032_Gen
    nativeHeatStep_hCoef_032_Gen nativeHeatStep_hFixed_032_Gen
    nativeHeatStep_hInit_032_Gen nativeHeatStep_hBase_032_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_032_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_032_Gen :
    nativeHeatY0Gen 32 = nativeShiftedFrame 1 (min nativeGap033Old.x nativeGap033Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_032_Gen, nativeHeatStep_hInd_032_Gen]

theorem nativeHeatStepFrameNum_032_Gen : NativeHeatStepFrameNum 32 := by
  have h1 := nativeHeatStep_hOld_032_Gen
  have h2 := nativeHeatStep_hInd_032_Gen
  have h3 := nativeHeatStep_hVar_032_Gen
  have h4 := nativeHeatStep_hQm_032_Gen
  have h5 := nativeHeatStep_hQN_032_Gen
  have h6 := nativeHeatStep_hY0_032_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_032_Gen : NativeHeatStepIndivNum 32 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 32 (by norm_num)) = nativeGap033Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_032_Gen]; exact nativeGap033Old_source
  · rw [hc, nativeHeatStep_hInd_032_Gen]; exact nativeGap033Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_032_Gen : nativeHeatY48Gen 32 = nativeHeat032Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_032_Gen, nativeHeatStep_hFr_032_Gen,
    nativeHeatStep_hCoef_032_Gen, nativeHeatStep_hFixed_032_Gen,
    nativeHeatStep_hBase_032_Gen]
  exact nativeHeat032All48

theorem nativeHeatResultGen_032 : nativeHeatResultGen 32 = nativeHeat032Result := by
  rw [← nativeHeat032Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_032_Gen, nativeHeatStep_hY0_032_Gen, nativeHeatStep_hExp_032_Gen,
    nativeHeatStep_hInit_032_Gen, nativeHeatStep_hFixed_032_Gen]

end ASDExplicitGamma.Native

end
