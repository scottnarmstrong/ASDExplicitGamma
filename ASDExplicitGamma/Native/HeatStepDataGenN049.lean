module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat049Complete
public import ASDExplicitGamma.Numerics.Native.Gap050Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_049_Gen : nativeHeatOldRowGen 49 = nativeGap050Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_049_Gen : nativeHeatIndividualGen 49 = nativeGap050Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_049_Gen : nativeHeatGenVariance 49 = nativeHeat049Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_049_Gen, nativeHeat049Variance_formula]

theorem nativeHeatStep_hSpec_049_Gen : nativeHeatGenSpectral 49 = nativeHeat049Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_049_Gen, nativeHeat049Variance_formula]

theorem nativeHeatStep_hQm_049_Gen : nativeHeatGenQm 49 = nativeHeat049Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_049_Gen, nativeHeatStep_hSpec_049_Gen,
    nativeHeat049Qm_formula]

theorem nativeHeatStep_hQN_049_Gen : nativeHeatQNGen 49 = nativeHeat049QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_049_Gen, nativeHeat049QN_formula]

theorem nativeHeatStep_hFr_049_Gen : nativeHeatFramesGen 49 = nativeHeat049Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_049_Gen, nativeHeatStep_hInd_049_Gen,
    nativeHeatStep_hVar_049_Gen, nativeHeatStep_hQN_049_Gen, nativeHeat049Frames_formula]

theorem nativeHeatStep_hArg_049_Gen : nativeHeatExpArgGen 49 = nativeHeatExpArg nativeGap050Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_049_Gen]

theorem nativeHeatStep_hExp_049_Gen : nativeHeatExpGen 49 = nativeHeat049Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_049_Gen, nativeHeat049Exp_formula]

theorem nativeHeatStep_hCoef_049_Gen : nativeHeatCoefGen 49 = nativeHeat049Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_049_Gen, nativeHeat049Coef_formula]

theorem nativeHeatStep_hInit_049_Gen : nativeHeatInitGen 49 = nativeHeat049Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_049_Gen, nativeHeatStep_hVar_049_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat049Init00_formula
    · exact nativeHeat049Init01_formula
    · exact nativeHeat049Init02_formula
    · exact nativeHeat049Init03_formula
    · exact nativeHeat049Init04_formula
    · exact nativeHeat049Init05_formula
    · exact nativeHeat049Init06_formula
    · exact nativeHeat049Init07_formula
    · exact nativeHeat049Init08_formula
    · exact nativeHeat049Init09_formula
    · exact nativeHeat049Init10_formula
    · exact nativeHeat049Init11_formula
    · exact nativeHeat049Init12_formula
    · exact nativeHeat049Init13_formula
    · exact nativeHeat049Init14_formula
    · exact nativeHeat049Init15_formula
    · exact nativeHeat049Init16_formula
    · exact nativeHeat049Init17_formula
    · exact nativeHeat049Init18_formula
    · exact nativeHeat049Init19_formula
    · exact nativeHeat049Init20_formula
theorem nativeHeatStep_hBase_049_Gen : nativeHeatBaseGen 49 = nativeHeat049Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_049_Gen, nativeHeatStep_hInit_049_Gen, nativeHeat049Base_formula]

theorem nativeHeatStep_hFixed_049_Gen : nativeHeatFixedGen 49 = nativeHeat049Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_049_Gen, nativeHeatStep_hFr_049_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat049Fixed01_formula
    · exact nativeHeat049Fixed02_formula
    · exact nativeHeat049Fixed03_formula
    · exact nativeHeat049Fixed04_formula
    · exact nativeHeat049Fixed05_formula
    · exact nativeHeat049Fixed06_formula
    · exact nativeHeat049Fixed07_formula
    · exact nativeHeat049Fixed08_formula
    · exact nativeHeat049Fixed09_formula
    · exact nativeHeat049Fixed10_formula
    · exact nativeHeat049Fixed11_formula
    · exact nativeHeat049Fixed12_formula
    · exact nativeHeat049Fixed13_formula
    · exact nativeHeat049Fixed14_formula
    · exact nativeHeat049Fixed15_formula
    · exact nativeHeat049Fixed16_formula
    · exact nativeHeat049Fixed17_formula
    · exact nativeHeat049Fixed18_formula
    · exact nativeHeat049Fixed19_formula
    · exact nativeHeat049Fixed20_formula

theorem nativeHeatStep_chk_049_Gen :
    nativeHeatPassRootsOk nativeGap050Old nativeHeat049Frames nativeHeat049Coef nativeHeat049Fixed nativeHeat049Base 48 nativeHeat049Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_049_Gen : NativeHeatStepPassNum 49 := by
  refine nativeHeatStepPassNum_of_literals 49 nativeGap050Old nativeHeat049Frames (nativeHeatExpArg nativeGap050Old)
    nativeHeat049Exp nativeHeat049Coef nativeHeat049Fixed nativeHeat049Init nativeHeat049Base nativeHeatStep_hOld_049_Gen
    nativeHeatStep_hFr_049_Gen nativeHeatStep_hArg_049_Gen nativeHeatStep_hExp_049_Gen
    nativeHeatStep_hCoef_049_Gen nativeHeatStep_hFixed_049_Gen
    nativeHeatStep_hInit_049_Gen nativeHeatStep_hBase_049_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_049_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_049_Gen :
    nativeHeatY0Gen 49 = nativeShiftedFrame 1 (min nativeGap050Old.x nativeGap050Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_049_Gen, nativeHeatStep_hInd_049_Gen]

theorem nativeHeatStepFrameNum_049_Gen : NativeHeatStepFrameNum 49 := by
  have h1 := nativeHeatStep_hOld_049_Gen
  have h2 := nativeHeatStep_hInd_049_Gen
  have h3 := nativeHeatStep_hVar_049_Gen
  have h4 := nativeHeatStep_hQm_049_Gen
  have h5 := nativeHeatStep_hQN_049_Gen
  have h6 := nativeHeatStep_hY0_049_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_049_Gen : NativeHeatStepIndivNum 49 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 49 (by norm_num)) = nativeGap050Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_049_Gen]; exact nativeGap050Old_source
  · rw [hc, nativeHeatStep_hInd_049_Gen]; exact nativeGap050Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_049_Gen : nativeHeatY48Gen 49 = nativeHeat049Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_049_Gen, nativeHeatStep_hFr_049_Gen,
    nativeHeatStep_hCoef_049_Gen, nativeHeatStep_hFixed_049_Gen,
    nativeHeatStep_hBase_049_Gen]
  exact nativeHeat049All48

theorem nativeHeatResultGen_049 : nativeHeatResultGen 49 = nativeHeat049Result := by
  rw [← nativeHeat049Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_049_Gen, nativeHeatStep_hY0_049_Gen, nativeHeatStep_hExp_049_Gen,
    nativeHeatStep_hInit_049_Gen, nativeHeatStep_hFixed_049_Gen]

end ASDExplicitGamma.Native

end
