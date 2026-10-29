module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat030Complete
public import ASDExplicitGamma.Numerics.Native.Gap031Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_030_Gen : nativeHeatOldRowGen 30 = nativeGap031Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_030_Gen : nativeHeatIndividualGen 30 = nativeGap031Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_030_Gen : nativeHeatGenVariance 30 = nativeHeat030Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_030_Gen, nativeHeat030Variance_formula]

theorem nativeHeatStep_hSpec_030_Gen : nativeHeatGenSpectral 30 = nativeHeat030Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_030_Gen, nativeHeat030Variance_formula]

theorem nativeHeatStep_hQm_030_Gen : nativeHeatGenQm 30 = nativeHeat030Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_030_Gen, nativeHeatStep_hSpec_030_Gen,
    nativeHeat030Qm_formula]

theorem nativeHeatStep_hQN_030_Gen : nativeHeatQNGen 30 = nativeHeat030QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_030_Gen, nativeHeat030QN_formula]

theorem nativeHeatStep_hFr_030_Gen : nativeHeatFramesGen 30 = nativeHeat030Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_030_Gen, nativeHeatStep_hInd_030_Gen,
    nativeHeatStep_hVar_030_Gen, nativeHeatStep_hQN_030_Gen, nativeHeat030Frames_formula]

theorem nativeHeatStep_hArg_030_Gen : nativeHeatExpArgGen 30 = nativeHeatExpArg nativeGap031Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_030_Gen]

theorem nativeHeatStep_hExp_030_Gen : nativeHeatExpGen 30 = nativeHeat030Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_030_Gen, nativeHeat030Exp_formula]

theorem nativeHeatStep_hCoef_030_Gen : nativeHeatCoefGen 30 = nativeHeat030Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_030_Gen, nativeHeat030Coef_formula]

theorem nativeHeatStep_hInit_030_Gen : nativeHeatInitGen 30 = nativeHeat030Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_030_Gen, nativeHeatStep_hVar_030_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat030Init00_formula
    · exact nativeHeat030Init01_formula
    · exact nativeHeat030Init02_formula
    · exact nativeHeat030Init03_formula
    · exact nativeHeat030Init04_formula
    · exact nativeHeat030Init05_formula
    · exact nativeHeat030Init06_formula
    · exact nativeHeat030Init07_formula
    · exact nativeHeat030Init08_formula
    · exact nativeHeat030Init09_formula
    · exact nativeHeat030Init10_formula
    · exact nativeHeat030Init11_formula
    · exact nativeHeat030Init12_formula
    · exact nativeHeat030Init13_formula
    · exact nativeHeat030Init14_formula
    · exact nativeHeat030Init15_formula
    · exact nativeHeat030Init16_formula
    · exact nativeHeat030Init17_formula
    · exact nativeHeat030Init18_formula
    · exact nativeHeat030Init19_formula
    · exact nativeHeat030Init20_formula
theorem nativeHeatStep_hBase_030_Gen : nativeHeatBaseGen 30 = nativeHeat030Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_030_Gen, nativeHeatStep_hInit_030_Gen, nativeHeat030Base_formula]

theorem nativeHeatStep_hFixed_030_Gen : nativeHeatFixedGen 30 = nativeHeat030Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_030_Gen, nativeHeatStep_hFr_030_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat030Fixed01_formula
    · exact nativeHeat030Fixed02_formula
    · exact nativeHeat030Fixed03_formula
    · exact nativeHeat030Fixed04_formula
    · exact nativeHeat030Fixed05_formula
    · exact nativeHeat030Fixed06_formula
    · exact nativeHeat030Fixed07_formula
    · exact nativeHeat030Fixed08_formula
    · exact nativeHeat030Fixed09_formula
    · exact nativeHeat030Fixed10_formula
    · exact nativeHeat030Fixed11_formula
    · exact nativeHeat030Fixed12_formula
    · exact nativeHeat030Fixed13_formula
    · exact nativeHeat030Fixed14_formula
    · exact nativeHeat030Fixed15_formula
    · exact nativeHeat030Fixed16_formula
    · exact nativeHeat030Fixed17_formula
    · exact nativeHeat030Fixed18_formula
    · exact nativeHeat030Fixed19_formula
    · exact nativeHeat030Fixed20_formula

theorem nativeHeatStep_chk_030_Gen :
    nativeHeatPassRootsOk nativeGap031Old nativeHeat030Frames nativeHeat030Coef nativeHeat030Fixed nativeHeat030Base 48 nativeHeat030Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_030_Gen : NativeHeatStepPassNum 30 := by
  refine nativeHeatStepPassNum_of_literals 30 nativeGap031Old nativeHeat030Frames (nativeHeatExpArg nativeGap031Old)
    nativeHeat030Exp nativeHeat030Coef nativeHeat030Fixed nativeHeat030Init nativeHeat030Base nativeHeatStep_hOld_030_Gen
    nativeHeatStep_hFr_030_Gen nativeHeatStep_hArg_030_Gen nativeHeatStep_hExp_030_Gen
    nativeHeatStep_hCoef_030_Gen nativeHeatStep_hFixed_030_Gen
    nativeHeatStep_hInit_030_Gen nativeHeatStep_hBase_030_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_030_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_030_Gen :
    nativeHeatY0Gen 30 = nativeShiftedFrame 1 (min nativeGap031Old.x nativeGap031Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_030_Gen, nativeHeatStep_hInd_030_Gen]

theorem nativeHeatStepFrameNum_030_Gen : NativeHeatStepFrameNum 30 := by
  have h1 := nativeHeatStep_hOld_030_Gen
  have h2 := nativeHeatStep_hInd_030_Gen
  have h3 := nativeHeatStep_hVar_030_Gen
  have h4 := nativeHeatStep_hQm_030_Gen
  have h5 := nativeHeatStep_hQN_030_Gen
  have h6 := nativeHeatStep_hY0_030_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_030_Gen : NativeHeatStepIndivNum 30 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 30 (by norm_num)) = nativeGap031Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_030_Gen]; exact nativeGap031Old_source
  · rw [hc, nativeHeatStep_hInd_030_Gen]; exact nativeGap031Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_030_Gen : nativeHeatY48Gen 30 = nativeHeat030Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_030_Gen, nativeHeatStep_hFr_030_Gen,
    nativeHeatStep_hCoef_030_Gen, nativeHeatStep_hFixed_030_Gen,
    nativeHeatStep_hBase_030_Gen]
  exact nativeHeat030All48

theorem nativeHeatResultGen_030 : nativeHeatResultGen 30 = nativeHeat030Result := by
  rw [← nativeHeat030Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_030_Gen, nativeHeatStep_hY0_030_Gen, nativeHeatStep_hExp_030_Gen,
    nativeHeatStep_hInit_030_Gen, nativeHeatStep_hFixed_030_Gen]

end ASDExplicitGamma.Native

end
