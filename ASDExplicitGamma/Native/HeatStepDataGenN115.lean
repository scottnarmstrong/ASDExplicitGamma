module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat115Complete
public import ASDExplicitGamma.Numerics.Native.Gap116Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_115_Gen : nativeHeatOldRowGen 115 = nativeGap116Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_115_Gen : nativeHeatIndividualGen 115 = nativeGap116Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_115_Gen : nativeHeatGenVariance 115 = nativeHeat115Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_115_Gen, nativeHeat115Variance_formula]

theorem nativeHeatStep_hSpec_115_Gen : nativeHeatGenSpectral 115 = nativeHeat115Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_115_Gen, nativeHeat115Variance_formula]

theorem nativeHeatStep_hQm_115_Gen : nativeHeatGenQm 115 = nativeHeat115Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_115_Gen, nativeHeatStep_hSpec_115_Gen,
    nativeHeat115Qm_formula]

theorem nativeHeatStep_hQN_115_Gen : nativeHeatQNGen 115 = nativeHeat115QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_115_Gen, nativeHeat115QN_formula]

theorem nativeHeatStep_hFr_115_Gen : nativeHeatFramesGen 115 = nativeHeat115Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_115_Gen, nativeHeatStep_hInd_115_Gen,
    nativeHeatStep_hVar_115_Gen, nativeHeatStep_hQN_115_Gen, nativeHeat115Frames_formula]

theorem nativeHeatStep_hArg_115_Gen : nativeHeatExpArgGen 115 = nativeHeatExpArg nativeGap116Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_115_Gen]

theorem nativeHeatStep_hExp_115_Gen : nativeHeatExpGen 115 = nativeHeat115Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_115_Gen, nativeHeat115Exp_formula]

theorem nativeHeatStep_hCoef_115_Gen : nativeHeatCoefGen 115 = nativeHeat115Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_115_Gen, nativeHeat115Coef_formula]

theorem nativeHeatStep_hInit_115_Gen : nativeHeatInitGen 115 = nativeHeat115Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_115_Gen, nativeHeatStep_hVar_115_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat115Init00_formula
    · exact nativeHeat115Init01_formula
    · exact nativeHeat115Init02_formula
    · exact nativeHeat115Init03_formula
    · exact nativeHeat115Init04_formula
    · exact nativeHeat115Init05_formula
    · exact nativeHeat115Init06_formula
    · exact nativeHeat115Init07_formula
    · exact nativeHeat115Init08_formula
    · exact nativeHeat115Init09_formula
    · exact nativeHeat115Init10_formula
    · exact nativeHeat115Init11_formula
    · exact nativeHeat115Init12_formula
    · exact nativeHeat115Init13_formula
    · exact nativeHeat115Init14_formula
    · exact nativeHeat115Init15_formula
    · exact nativeHeat115Init16_formula
    · exact nativeHeat115Init17_formula
    · exact nativeHeat115Init18_formula
    · exact nativeHeat115Init19_formula
    · exact nativeHeat115Init20_formula
theorem nativeHeatStep_hBase_115_Gen : nativeHeatBaseGen 115 = nativeHeat115Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_115_Gen, nativeHeatStep_hInit_115_Gen, nativeHeat115Base_formula]

theorem nativeHeatStep_hFixed_115_Gen : nativeHeatFixedGen 115 = nativeHeat115Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_115_Gen, nativeHeatStep_hFr_115_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat115Fixed01_formula
    · exact nativeHeat115Fixed02_formula
    · exact nativeHeat115Fixed03_formula
    · exact nativeHeat115Fixed04_formula
    · exact nativeHeat115Fixed05_formula
    · exact nativeHeat115Fixed06_formula
    · exact nativeHeat115Fixed07_formula
    · exact nativeHeat115Fixed08_formula
    · exact nativeHeat115Fixed09_formula
    · exact nativeHeat115Fixed10_formula
    · exact nativeHeat115Fixed11_formula
    · exact nativeHeat115Fixed12_formula
    · exact nativeHeat115Fixed13_formula
    · exact nativeHeat115Fixed14_formula
    · exact nativeHeat115Fixed15_formula
    · exact nativeHeat115Fixed16_formula
    · exact nativeHeat115Fixed17_formula
    · exact nativeHeat115Fixed18_formula
    · exact nativeHeat115Fixed19_formula
    · exact nativeHeat115Fixed20_formula

theorem nativeHeatStep_chk_115_Gen :
    nativeHeatPassRootsOk nativeGap116Old nativeHeat115Frames nativeHeat115Coef nativeHeat115Fixed nativeHeat115Base 48 nativeHeat115Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_115_Gen : NativeHeatStepPassNum 115 := by
  refine nativeHeatStepPassNum_of_literals 115 nativeGap116Old nativeHeat115Frames (nativeHeatExpArg nativeGap116Old)
    nativeHeat115Exp nativeHeat115Coef nativeHeat115Fixed nativeHeat115Init nativeHeat115Base nativeHeatStep_hOld_115_Gen
    nativeHeatStep_hFr_115_Gen nativeHeatStep_hArg_115_Gen nativeHeatStep_hExp_115_Gen
    nativeHeatStep_hCoef_115_Gen nativeHeatStep_hFixed_115_Gen
    nativeHeatStep_hInit_115_Gen nativeHeatStep_hBase_115_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_115_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_115_Gen :
    nativeHeatY0Gen 115 = nativeShiftedFrame 1 (min nativeGap116Old.x nativeGap116Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_115_Gen, nativeHeatStep_hInd_115_Gen]

theorem nativeHeatStepFrameNum_115_Gen : NativeHeatStepFrameNum 115 := by
  have h1 := nativeHeatStep_hOld_115_Gen
  have h2 := nativeHeatStep_hInd_115_Gen
  have h3 := nativeHeatStep_hVar_115_Gen
  have h4 := nativeHeatStep_hQm_115_Gen
  have h5 := nativeHeatStep_hQN_115_Gen
  have h6 := nativeHeatStep_hY0_115_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_115_Gen : NativeHeatStepIndivNum 115 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 115 (by norm_num)) = nativeGap116Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_115_Gen]; exact nativeGap116Old_source
  · rw [hc, nativeHeatStep_hInd_115_Gen]; exact nativeGap116Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_115_Gen : nativeHeatY48Gen 115 = nativeHeat115Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_115_Gen, nativeHeatStep_hFr_115_Gen,
    nativeHeatStep_hCoef_115_Gen, nativeHeatStep_hFixed_115_Gen,
    nativeHeatStep_hBase_115_Gen]
  exact nativeHeat115All48

theorem nativeHeatResultGen_115 : nativeHeatResultGen 115 = nativeHeat115Result := by
  rw [← nativeHeat115Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_115_Gen, nativeHeatStep_hY0_115_Gen, nativeHeatStep_hExp_115_Gen,
    nativeHeatStep_hInit_115_Gen, nativeHeatStep_hFixed_115_Gen]

end ASDExplicitGamma.Native

end
