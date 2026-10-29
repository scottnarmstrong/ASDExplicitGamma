module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat158Complete
public import ASDExplicitGamma.Numerics.Native.Gap159Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_158_Gen : nativeHeatOldRowGen 158 = nativeGap159Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_158_Gen : nativeHeatIndividualGen 158 = nativeGap159Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_158_Gen : nativeHeatGenVariance 158 = nativeHeat158Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_158_Gen, nativeHeat158Variance_formula]

theorem nativeHeatStep_hSpec_158_Gen : nativeHeatGenSpectral 158 = nativeHeat158Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_158_Gen, nativeHeat158Variance_formula]

theorem nativeHeatStep_hQm_158_Gen : nativeHeatGenQm 158 = nativeHeat158Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_158_Gen, nativeHeatStep_hSpec_158_Gen,
    nativeHeat158Qm_formula]

theorem nativeHeatStep_hQN_158_Gen : nativeHeatQNGen 158 = nativeHeat158QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_158_Gen, nativeHeat158QN_formula]

theorem nativeHeatStep_hFr_158_Gen : nativeHeatFramesGen 158 = nativeHeat158Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_158_Gen, nativeHeatStep_hInd_158_Gen,
    nativeHeatStep_hVar_158_Gen, nativeHeatStep_hQN_158_Gen, nativeHeat158Frames_formula]

theorem nativeHeatStep_hArg_158_Gen : nativeHeatExpArgGen 158 = nativeHeatExpArg nativeGap159Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_158_Gen]

theorem nativeHeatStep_hExp_158_Gen : nativeHeatExpGen 158 = nativeHeat158Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_158_Gen, nativeHeat158Exp_formula]

theorem nativeHeatStep_hCoef_158_Gen : nativeHeatCoefGen 158 = nativeHeat158Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_158_Gen, nativeHeat158Coef_formula]

theorem nativeHeatStep_hInit_158_Gen : nativeHeatInitGen 158 = nativeHeat158Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_158_Gen, nativeHeatStep_hVar_158_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat158Init00_formula
    · exact nativeHeat158Init01_formula
    · exact nativeHeat158Init02_formula
    · exact nativeHeat158Init03_formula
    · exact nativeHeat158Init04_formula
    · exact nativeHeat158Init05_formula
    · exact nativeHeat158Init06_formula
    · exact nativeHeat158Init07_formula
    · exact nativeHeat158Init08_formula
    · exact nativeHeat158Init09_formula
    · exact nativeHeat158Init10_formula
    · exact nativeHeat158Init11_formula
    · exact nativeHeat158Init12_formula
    · exact nativeHeat158Init13_formula
    · exact nativeHeat158Init14_formula
    · exact nativeHeat158Init15_formula
    · exact nativeHeat158Init16_formula
    · exact nativeHeat158Init17_formula
    · exact nativeHeat158Init18_formula
    · exact nativeHeat158Init19_formula
    · exact nativeHeat158Init20_formula
theorem nativeHeatStep_hBase_158_Gen : nativeHeatBaseGen 158 = nativeHeat158Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_158_Gen, nativeHeatStep_hInit_158_Gen, nativeHeat158Base_formula]

theorem nativeHeatStep_hFixed_158_Gen : nativeHeatFixedGen 158 = nativeHeat158Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_158_Gen, nativeHeatStep_hFr_158_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat158Fixed01_formula
    · exact nativeHeat158Fixed02_formula
    · exact nativeHeat158Fixed03_formula
    · exact nativeHeat158Fixed04_formula
    · exact nativeHeat158Fixed05_formula
    · exact nativeHeat158Fixed06_formula
    · exact nativeHeat158Fixed07_formula
    · exact nativeHeat158Fixed08_formula
    · exact nativeHeat158Fixed09_formula
    · exact nativeHeat158Fixed10_formula
    · exact nativeHeat158Fixed11_formula
    · exact nativeHeat158Fixed12_formula
    · exact nativeHeat158Fixed13_formula
    · exact nativeHeat158Fixed14_formula
    · exact nativeHeat158Fixed15_formula
    · exact nativeHeat158Fixed16_formula
    · exact nativeHeat158Fixed17_formula
    · exact nativeHeat158Fixed18_formula
    · exact nativeHeat158Fixed19_formula
    · exact nativeHeat158Fixed20_formula

theorem nativeHeatStep_chk_158_Gen :
    nativeHeatPassRootsOk nativeGap159Old nativeHeat158Frames nativeHeat158Coef nativeHeat158Fixed nativeHeat158Base 48 nativeHeat158Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_158_Gen : NativeHeatStepPassNum 158 := by
  refine nativeHeatStepPassNum_of_literals 158 nativeGap159Old nativeHeat158Frames (nativeHeatExpArg nativeGap159Old)
    nativeHeat158Exp nativeHeat158Coef nativeHeat158Fixed nativeHeat158Init nativeHeat158Base nativeHeatStep_hOld_158_Gen
    nativeHeatStep_hFr_158_Gen nativeHeatStep_hArg_158_Gen nativeHeatStep_hExp_158_Gen
    nativeHeatStep_hCoef_158_Gen nativeHeatStep_hFixed_158_Gen
    nativeHeatStep_hInit_158_Gen nativeHeatStep_hBase_158_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_158_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_158_Gen :
    nativeHeatY0Gen 158 = nativeShiftedFrame 1 (min nativeGap159Old.x nativeGap159Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_158_Gen, nativeHeatStep_hInd_158_Gen]

theorem nativeHeatStepFrameNum_158_Gen : NativeHeatStepFrameNum 158 := by
  have h1 := nativeHeatStep_hOld_158_Gen
  have h2 := nativeHeatStep_hInd_158_Gen
  have h3 := nativeHeatStep_hVar_158_Gen
  have h4 := nativeHeatStep_hQm_158_Gen
  have h5 := nativeHeatStep_hQN_158_Gen
  have h6 := nativeHeatStep_hY0_158_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_158_Gen : NativeHeatStepIndivNum 158 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 158 (by norm_num)) = nativeGap159Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_158_Gen]; exact nativeGap159Old_source
  · rw [hc, nativeHeatStep_hInd_158_Gen]; exact nativeGap159Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_158_Gen : nativeHeatY48Gen 158 = nativeHeat158Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_158_Gen, nativeHeatStep_hFr_158_Gen,
    nativeHeatStep_hCoef_158_Gen, nativeHeatStep_hFixed_158_Gen,
    nativeHeatStep_hBase_158_Gen]
  exact nativeHeat158All48

theorem nativeHeatResultGen_158 : nativeHeatResultGen 158 = nativeHeat158Result := by
  rw [← nativeHeat158Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_158_Gen, nativeHeatStep_hY0_158_Gen, nativeHeatStep_hExp_158_Gen,
    nativeHeatStep_hInit_158_Gen, nativeHeatStep_hFixed_158_Gen]

end ASDExplicitGamma.Native

end
