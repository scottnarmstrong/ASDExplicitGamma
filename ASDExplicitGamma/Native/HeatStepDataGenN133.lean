module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat133Complete
public import ASDExplicitGamma.Numerics.Native.Gap134Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_133_Gen : nativeHeatOldRowGen 133 = nativeGap134Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_133_Gen : nativeHeatIndividualGen 133 = nativeGap134Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_133_Gen : nativeHeatGenVariance 133 = nativeHeat133Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_133_Gen, nativeHeat133Variance_formula]

theorem nativeHeatStep_hSpec_133_Gen : nativeHeatGenSpectral 133 = nativeHeat133Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_133_Gen, nativeHeat133Variance_formula]

theorem nativeHeatStep_hQm_133_Gen : nativeHeatGenQm 133 = nativeHeat133Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_133_Gen, nativeHeatStep_hSpec_133_Gen,
    nativeHeat133Qm_formula]

theorem nativeHeatStep_hQN_133_Gen : nativeHeatQNGen 133 = nativeHeat133QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_133_Gen, nativeHeat133QN_formula]

theorem nativeHeatStep_hFr_133_Gen : nativeHeatFramesGen 133 = nativeHeat133Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_133_Gen, nativeHeatStep_hInd_133_Gen,
    nativeHeatStep_hVar_133_Gen, nativeHeatStep_hQN_133_Gen, nativeHeat133Frames_formula]

theorem nativeHeatStep_hArg_133_Gen : nativeHeatExpArgGen 133 = nativeHeatExpArg nativeGap134Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_133_Gen]

theorem nativeHeatStep_hExp_133_Gen : nativeHeatExpGen 133 = nativeHeat133Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_133_Gen, nativeHeat133Exp_formula]

theorem nativeHeatStep_hCoef_133_Gen : nativeHeatCoefGen 133 = nativeHeat133Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_133_Gen, nativeHeat133Coef_formula]

theorem nativeHeatStep_hInit_133_Gen : nativeHeatInitGen 133 = nativeHeat133Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_133_Gen, nativeHeatStep_hVar_133_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat133Init00_formula
    · exact nativeHeat133Init01_formula
    · exact nativeHeat133Init02_formula
    · exact nativeHeat133Init03_formula
    · exact nativeHeat133Init04_formula
    · exact nativeHeat133Init05_formula
    · exact nativeHeat133Init06_formula
    · exact nativeHeat133Init07_formula
    · exact nativeHeat133Init08_formula
    · exact nativeHeat133Init09_formula
    · exact nativeHeat133Init10_formula
    · exact nativeHeat133Init11_formula
    · exact nativeHeat133Init12_formula
    · exact nativeHeat133Init13_formula
    · exact nativeHeat133Init14_formula
    · exact nativeHeat133Init15_formula
    · exact nativeHeat133Init16_formula
    · exact nativeHeat133Init17_formula
    · exact nativeHeat133Init18_formula
    · exact nativeHeat133Init19_formula
    · exact nativeHeat133Init20_formula
theorem nativeHeatStep_hBase_133_Gen : nativeHeatBaseGen 133 = nativeHeat133Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_133_Gen, nativeHeatStep_hInit_133_Gen, nativeHeat133Base_formula]

theorem nativeHeatStep_hFixed_133_Gen : nativeHeatFixedGen 133 = nativeHeat133Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_133_Gen, nativeHeatStep_hFr_133_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat133Fixed01_formula
    · exact nativeHeat133Fixed02_formula
    · exact nativeHeat133Fixed03_formula
    · exact nativeHeat133Fixed04_formula
    · exact nativeHeat133Fixed05_formula
    · exact nativeHeat133Fixed06_formula
    · exact nativeHeat133Fixed07_formula
    · exact nativeHeat133Fixed08_formula
    · exact nativeHeat133Fixed09_formula
    · exact nativeHeat133Fixed10_formula
    · exact nativeHeat133Fixed11_formula
    · exact nativeHeat133Fixed12_formula
    · exact nativeHeat133Fixed13_formula
    · exact nativeHeat133Fixed14_formula
    · exact nativeHeat133Fixed15_formula
    · exact nativeHeat133Fixed16_formula
    · exact nativeHeat133Fixed17_formula
    · exact nativeHeat133Fixed18_formula
    · exact nativeHeat133Fixed19_formula
    · exact nativeHeat133Fixed20_formula

theorem nativeHeatStep_chk_133_Gen :
    nativeHeatPassRootsOk nativeGap134Old nativeHeat133Frames nativeHeat133Coef nativeHeat133Fixed nativeHeat133Base 48 nativeHeat133Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_133_Gen : NativeHeatStepPassNum 133 := by
  refine nativeHeatStepPassNum_of_literals 133 nativeGap134Old nativeHeat133Frames (nativeHeatExpArg nativeGap134Old)
    nativeHeat133Exp nativeHeat133Coef nativeHeat133Fixed nativeHeat133Init nativeHeat133Base nativeHeatStep_hOld_133_Gen
    nativeHeatStep_hFr_133_Gen nativeHeatStep_hArg_133_Gen nativeHeatStep_hExp_133_Gen
    nativeHeatStep_hCoef_133_Gen nativeHeatStep_hFixed_133_Gen
    nativeHeatStep_hInit_133_Gen nativeHeatStep_hBase_133_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_133_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_133_Gen :
    nativeHeatY0Gen 133 = nativeShiftedFrame 1 (min nativeGap134Old.x nativeGap134Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_133_Gen, nativeHeatStep_hInd_133_Gen]

theorem nativeHeatStepFrameNum_133_Gen : NativeHeatStepFrameNum 133 := by
  have h1 := nativeHeatStep_hOld_133_Gen
  have h2 := nativeHeatStep_hInd_133_Gen
  have h3 := nativeHeatStep_hVar_133_Gen
  have h4 := nativeHeatStep_hQm_133_Gen
  have h5 := nativeHeatStep_hQN_133_Gen
  have h6 := nativeHeatStep_hY0_133_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_133_Gen : NativeHeatStepIndivNum 133 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 133 (by norm_num)) = nativeGap134Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_133_Gen]; exact nativeGap134Old_source
  · rw [hc, nativeHeatStep_hInd_133_Gen]; exact nativeGap134Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_133_Gen : nativeHeatY48Gen 133 = nativeHeat133Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_133_Gen, nativeHeatStep_hFr_133_Gen,
    nativeHeatStep_hCoef_133_Gen, nativeHeatStep_hFixed_133_Gen,
    nativeHeatStep_hBase_133_Gen]
  exact nativeHeat133All48

theorem nativeHeatResultGen_133 : nativeHeatResultGen 133 = nativeHeat133Result := by
  rw [← nativeHeat133Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_133_Gen, nativeHeatStep_hY0_133_Gen, nativeHeatStep_hExp_133_Gen,
    nativeHeatStep_hInit_133_Gen, nativeHeatStep_hFixed_133_Gen]

end ASDExplicitGamma.Native

end
