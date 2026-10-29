module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat108Complete
public import ASDExplicitGamma.Numerics.Native.Gap109Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_108_Gen : nativeHeatOldRowGen 108 = nativeGap109Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_108_Gen : nativeHeatIndividualGen 108 = nativeGap109Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_108_Gen : nativeHeatGenVariance 108 = nativeHeat108Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_108_Gen, nativeHeat108Variance_formula]

theorem nativeHeatStep_hSpec_108_Gen : nativeHeatGenSpectral 108 = nativeHeat108Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_108_Gen, nativeHeat108Variance_formula]

theorem nativeHeatStep_hQm_108_Gen : nativeHeatGenQm 108 = nativeHeat108Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_108_Gen, nativeHeatStep_hSpec_108_Gen,
    nativeHeat108Qm_formula]

theorem nativeHeatStep_hQN_108_Gen : nativeHeatQNGen 108 = nativeHeat108QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_108_Gen, nativeHeat108QN_formula]

theorem nativeHeatStep_hFr_108_Gen : nativeHeatFramesGen 108 = nativeHeat108Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_108_Gen, nativeHeatStep_hInd_108_Gen,
    nativeHeatStep_hVar_108_Gen, nativeHeatStep_hQN_108_Gen, nativeHeat108Frames_formula]

theorem nativeHeatStep_hArg_108_Gen : nativeHeatExpArgGen 108 = nativeHeatExpArg nativeGap109Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_108_Gen]

theorem nativeHeatStep_hExp_108_Gen : nativeHeatExpGen 108 = nativeHeat108Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_108_Gen, nativeHeat108Exp_formula]

theorem nativeHeatStep_hCoef_108_Gen : nativeHeatCoefGen 108 = nativeHeat108Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_108_Gen, nativeHeat108Coef_formula]

theorem nativeHeatStep_hInit_108_Gen : nativeHeatInitGen 108 = nativeHeat108Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_108_Gen, nativeHeatStep_hVar_108_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat108Init00_formula
    · exact nativeHeat108Init01_formula
    · exact nativeHeat108Init02_formula
    · exact nativeHeat108Init03_formula
    · exact nativeHeat108Init04_formula
    · exact nativeHeat108Init05_formula
    · exact nativeHeat108Init06_formula
    · exact nativeHeat108Init07_formula
    · exact nativeHeat108Init08_formula
    · exact nativeHeat108Init09_formula
    · exact nativeHeat108Init10_formula
    · exact nativeHeat108Init11_formula
    · exact nativeHeat108Init12_formula
    · exact nativeHeat108Init13_formula
    · exact nativeHeat108Init14_formula
    · exact nativeHeat108Init15_formula
    · exact nativeHeat108Init16_formula
    · exact nativeHeat108Init17_formula
    · exact nativeHeat108Init18_formula
    · exact nativeHeat108Init19_formula
    · exact nativeHeat108Init20_formula
theorem nativeHeatStep_hBase_108_Gen : nativeHeatBaseGen 108 = nativeHeat108Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_108_Gen, nativeHeatStep_hInit_108_Gen, nativeHeat108Base_formula]

theorem nativeHeatStep_hFixed_108_Gen : nativeHeatFixedGen 108 = nativeHeat108Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_108_Gen, nativeHeatStep_hFr_108_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat108Fixed01_formula
    · exact nativeHeat108Fixed02_formula
    · exact nativeHeat108Fixed03_formula
    · exact nativeHeat108Fixed04_formula
    · exact nativeHeat108Fixed05_formula
    · exact nativeHeat108Fixed06_formula
    · exact nativeHeat108Fixed07_formula
    · exact nativeHeat108Fixed08_formula
    · exact nativeHeat108Fixed09_formula
    · exact nativeHeat108Fixed10_formula
    · exact nativeHeat108Fixed11_formula
    · exact nativeHeat108Fixed12_formula
    · exact nativeHeat108Fixed13_formula
    · exact nativeHeat108Fixed14_formula
    · exact nativeHeat108Fixed15_formula
    · exact nativeHeat108Fixed16_formula
    · exact nativeHeat108Fixed17_formula
    · exact nativeHeat108Fixed18_formula
    · exact nativeHeat108Fixed19_formula
    · exact nativeHeat108Fixed20_formula

theorem nativeHeatStep_chk_108_Gen :
    nativeHeatPassRootsOk nativeGap109Old nativeHeat108Frames nativeHeat108Coef nativeHeat108Fixed nativeHeat108Base 48 nativeHeat108Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_108_Gen : NativeHeatStepPassNum 108 := by
  refine nativeHeatStepPassNum_of_literals 108 nativeGap109Old nativeHeat108Frames (nativeHeatExpArg nativeGap109Old)
    nativeHeat108Exp nativeHeat108Coef nativeHeat108Fixed nativeHeat108Init nativeHeat108Base nativeHeatStep_hOld_108_Gen
    nativeHeatStep_hFr_108_Gen nativeHeatStep_hArg_108_Gen nativeHeatStep_hExp_108_Gen
    nativeHeatStep_hCoef_108_Gen nativeHeatStep_hFixed_108_Gen
    nativeHeatStep_hInit_108_Gen nativeHeatStep_hBase_108_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_108_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_108_Gen :
    nativeHeatY0Gen 108 = nativeShiftedFrame 1 (min nativeGap109Old.x nativeGap109Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_108_Gen, nativeHeatStep_hInd_108_Gen]

theorem nativeHeatStepFrameNum_108_Gen : NativeHeatStepFrameNum 108 := by
  have h1 := nativeHeatStep_hOld_108_Gen
  have h2 := nativeHeatStep_hInd_108_Gen
  have h3 := nativeHeatStep_hVar_108_Gen
  have h4 := nativeHeatStep_hQm_108_Gen
  have h5 := nativeHeatStep_hQN_108_Gen
  have h6 := nativeHeatStep_hY0_108_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_108_Gen : NativeHeatStepIndivNum 108 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 108 (by norm_num)) = nativeGap109Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_108_Gen]; exact nativeGap109Old_source
  · rw [hc, nativeHeatStep_hInd_108_Gen]; exact nativeGap109Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_108_Gen : nativeHeatY48Gen 108 = nativeHeat108Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_108_Gen, nativeHeatStep_hFr_108_Gen,
    nativeHeatStep_hCoef_108_Gen, nativeHeatStep_hFixed_108_Gen,
    nativeHeatStep_hBase_108_Gen]
  exact nativeHeat108All48

theorem nativeHeatResultGen_108 : nativeHeatResultGen 108 = nativeHeat108Result := by
  rw [← nativeHeat108Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_108_Gen, nativeHeatStep_hY0_108_Gen, nativeHeatStep_hExp_108_Gen,
    nativeHeatStep_hInit_108_Gen, nativeHeatStep_hFixed_108_Gen]

end ASDExplicitGamma.Native

end
