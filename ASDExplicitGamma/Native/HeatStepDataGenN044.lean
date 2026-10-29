module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat044Complete
public import ASDExplicitGamma.Numerics.Native.Gap045Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_044_Gen : nativeHeatOldRowGen 44 = nativeGap045Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_044_Gen : nativeHeatIndividualGen 44 = nativeGap045Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_044_Gen : nativeHeatGenVariance 44 = nativeHeat044Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_044_Gen, nativeHeat044Variance_formula]

theorem nativeHeatStep_hSpec_044_Gen : nativeHeatGenSpectral 44 = nativeHeat044Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_044_Gen, nativeHeat044Variance_formula]

theorem nativeHeatStep_hQm_044_Gen : nativeHeatGenQm 44 = nativeHeat044Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_044_Gen, nativeHeatStep_hSpec_044_Gen,
    nativeHeat044Qm_formula]

theorem nativeHeatStep_hQN_044_Gen : nativeHeatQNGen 44 = nativeHeat044QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_044_Gen, nativeHeat044QN_formula]

theorem nativeHeatStep_hFr_044_Gen : nativeHeatFramesGen 44 = nativeHeat044Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_044_Gen, nativeHeatStep_hInd_044_Gen,
    nativeHeatStep_hVar_044_Gen, nativeHeatStep_hQN_044_Gen, nativeHeat044Frames_formula]

theorem nativeHeatStep_hArg_044_Gen : nativeHeatExpArgGen 44 = nativeHeatExpArg nativeGap045Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_044_Gen]

theorem nativeHeatStep_hExp_044_Gen : nativeHeatExpGen 44 = nativeHeat044Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_044_Gen, nativeHeat044Exp_formula]

theorem nativeHeatStep_hCoef_044_Gen : nativeHeatCoefGen 44 = nativeHeat044Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_044_Gen, nativeHeat044Coef_formula]

theorem nativeHeatStep_hInit_044_Gen : nativeHeatInitGen 44 = nativeHeat044Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_044_Gen, nativeHeatStep_hVar_044_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat044Init00_formula
    · exact nativeHeat044Init01_formula
    · exact nativeHeat044Init02_formula
    · exact nativeHeat044Init03_formula
    · exact nativeHeat044Init04_formula
    · exact nativeHeat044Init05_formula
    · exact nativeHeat044Init06_formula
    · exact nativeHeat044Init07_formula
    · exact nativeHeat044Init08_formula
    · exact nativeHeat044Init09_formula
    · exact nativeHeat044Init10_formula
    · exact nativeHeat044Init11_formula
    · exact nativeHeat044Init12_formula
    · exact nativeHeat044Init13_formula
    · exact nativeHeat044Init14_formula
    · exact nativeHeat044Init15_formula
    · exact nativeHeat044Init16_formula
    · exact nativeHeat044Init17_formula
    · exact nativeHeat044Init18_formula
    · exact nativeHeat044Init19_formula
    · exact nativeHeat044Init20_formula
theorem nativeHeatStep_hBase_044_Gen : nativeHeatBaseGen 44 = nativeHeat044Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_044_Gen, nativeHeatStep_hInit_044_Gen, nativeHeat044Base_formula]

theorem nativeHeatStep_hFixed_044_Gen : nativeHeatFixedGen 44 = nativeHeat044Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_044_Gen, nativeHeatStep_hFr_044_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat044Fixed01_formula
    · exact nativeHeat044Fixed02_formula
    · exact nativeHeat044Fixed03_formula
    · exact nativeHeat044Fixed04_formula
    · exact nativeHeat044Fixed05_formula
    · exact nativeHeat044Fixed06_formula
    · exact nativeHeat044Fixed07_formula
    · exact nativeHeat044Fixed08_formula
    · exact nativeHeat044Fixed09_formula
    · exact nativeHeat044Fixed10_formula
    · exact nativeHeat044Fixed11_formula
    · exact nativeHeat044Fixed12_formula
    · exact nativeHeat044Fixed13_formula
    · exact nativeHeat044Fixed14_formula
    · exact nativeHeat044Fixed15_formula
    · exact nativeHeat044Fixed16_formula
    · exact nativeHeat044Fixed17_formula
    · exact nativeHeat044Fixed18_formula
    · exact nativeHeat044Fixed19_formula
    · exact nativeHeat044Fixed20_formula

theorem nativeHeatStep_chk_044_Gen :
    nativeHeatPassRootsOk nativeGap045Old nativeHeat044Frames nativeHeat044Coef nativeHeat044Fixed nativeHeat044Base 48 nativeHeat044Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_044_Gen : NativeHeatStepPassNum 44 := by
  refine nativeHeatStepPassNum_of_literals 44 nativeGap045Old nativeHeat044Frames (nativeHeatExpArg nativeGap045Old)
    nativeHeat044Exp nativeHeat044Coef nativeHeat044Fixed nativeHeat044Init nativeHeat044Base nativeHeatStep_hOld_044_Gen
    nativeHeatStep_hFr_044_Gen nativeHeatStep_hArg_044_Gen nativeHeatStep_hExp_044_Gen
    nativeHeatStep_hCoef_044_Gen nativeHeatStep_hFixed_044_Gen
    nativeHeatStep_hInit_044_Gen nativeHeatStep_hBase_044_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_044_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_044_Gen :
    nativeHeatY0Gen 44 = nativeShiftedFrame 1 (min nativeGap045Old.x nativeGap045Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_044_Gen, nativeHeatStep_hInd_044_Gen]

theorem nativeHeatStepFrameNum_044_Gen : NativeHeatStepFrameNum 44 := by
  have h1 := nativeHeatStep_hOld_044_Gen
  have h2 := nativeHeatStep_hInd_044_Gen
  have h3 := nativeHeatStep_hVar_044_Gen
  have h4 := nativeHeatStep_hQm_044_Gen
  have h5 := nativeHeatStep_hQN_044_Gen
  have h6 := nativeHeatStep_hY0_044_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_044_Gen : NativeHeatStepIndivNum 44 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 44 (by norm_num)) = nativeGap045Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_044_Gen]; exact nativeGap045Old_source
  · rw [hc, nativeHeatStep_hInd_044_Gen]; exact nativeGap045Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_044_Gen : nativeHeatY48Gen 44 = nativeHeat044Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_044_Gen, nativeHeatStep_hFr_044_Gen,
    nativeHeatStep_hCoef_044_Gen, nativeHeatStep_hFixed_044_Gen,
    nativeHeatStep_hBase_044_Gen]
  exact nativeHeat044All48

theorem nativeHeatResultGen_044 : nativeHeatResultGen 44 = nativeHeat044Result := by
  rw [← nativeHeat044Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_044_Gen, nativeHeatStep_hY0_044_Gen, nativeHeatStep_hExp_044_Gen,
    nativeHeatStep_hInit_044_Gen, nativeHeatStep_hFixed_044_Gen]

end ASDExplicitGamma.Native

end
