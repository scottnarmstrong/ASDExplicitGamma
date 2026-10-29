module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat148Complete
public import ASDExplicitGamma.Numerics.Native.Gap149Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_148_Gen : nativeHeatOldRowGen 148 = nativeGap149Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_148_Gen : nativeHeatIndividualGen 148 = nativeGap149Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_148_Gen : nativeHeatGenVariance 148 = nativeHeat148Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_148_Gen, nativeHeat148Variance_formula]

theorem nativeHeatStep_hSpec_148_Gen : nativeHeatGenSpectral 148 = nativeHeat148Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_148_Gen, nativeHeat148Variance_formula]

theorem nativeHeatStep_hQm_148_Gen : nativeHeatGenQm 148 = nativeHeat148Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_148_Gen, nativeHeatStep_hSpec_148_Gen,
    nativeHeat148Qm_formula]

theorem nativeHeatStep_hQN_148_Gen : nativeHeatQNGen 148 = nativeHeat148QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_148_Gen, nativeHeat148QN_formula]

theorem nativeHeatStep_hFr_148_Gen : nativeHeatFramesGen 148 = nativeHeat148Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_148_Gen, nativeHeatStep_hInd_148_Gen,
    nativeHeatStep_hVar_148_Gen, nativeHeatStep_hQN_148_Gen, nativeHeat148Frames_formula]

theorem nativeHeatStep_hArg_148_Gen : nativeHeatExpArgGen 148 = nativeHeatExpArg nativeGap149Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_148_Gen]

theorem nativeHeatStep_hExp_148_Gen : nativeHeatExpGen 148 = nativeHeat148Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_148_Gen, nativeHeat148Exp_formula]

theorem nativeHeatStep_hCoef_148_Gen : nativeHeatCoefGen 148 = nativeHeat148Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_148_Gen, nativeHeat148Coef_formula]

theorem nativeHeatStep_hInit_148_Gen : nativeHeatInitGen 148 = nativeHeat148Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_148_Gen, nativeHeatStep_hVar_148_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat148Init00_formula
    · exact nativeHeat148Init01_formula
    · exact nativeHeat148Init02_formula
    · exact nativeHeat148Init03_formula
    · exact nativeHeat148Init04_formula
    · exact nativeHeat148Init05_formula
    · exact nativeHeat148Init06_formula
    · exact nativeHeat148Init07_formula
    · exact nativeHeat148Init08_formula
    · exact nativeHeat148Init09_formula
    · exact nativeHeat148Init10_formula
    · exact nativeHeat148Init11_formula
    · exact nativeHeat148Init12_formula
    · exact nativeHeat148Init13_formula
    · exact nativeHeat148Init14_formula
    · exact nativeHeat148Init15_formula
    · exact nativeHeat148Init16_formula
    · exact nativeHeat148Init17_formula
    · exact nativeHeat148Init18_formula
    · exact nativeHeat148Init19_formula
    · exact nativeHeat148Init20_formula
theorem nativeHeatStep_hBase_148_Gen : nativeHeatBaseGen 148 = nativeHeat148Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_148_Gen, nativeHeatStep_hInit_148_Gen, nativeHeat148Base_formula]

theorem nativeHeatStep_hFixed_148_Gen : nativeHeatFixedGen 148 = nativeHeat148Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_148_Gen, nativeHeatStep_hFr_148_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat148Fixed01_formula
    · exact nativeHeat148Fixed02_formula
    · exact nativeHeat148Fixed03_formula
    · exact nativeHeat148Fixed04_formula
    · exact nativeHeat148Fixed05_formula
    · exact nativeHeat148Fixed06_formula
    · exact nativeHeat148Fixed07_formula
    · exact nativeHeat148Fixed08_formula
    · exact nativeHeat148Fixed09_formula
    · exact nativeHeat148Fixed10_formula
    · exact nativeHeat148Fixed11_formula
    · exact nativeHeat148Fixed12_formula
    · exact nativeHeat148Fixed13_formula
    · exact nativeHeat148Fixed14_formula
    · exact nativeHeat148Fixed15_formula
    · exact nativeHeat148Fixed16_formula
    · exact nativeHeat148Fixed17_formula
    · exact nativeHeat148Fixed18_formula
    · exact nativeHeat148Fixed19_formula
    · exact nativeHeat148Fixed20_formula

theorem nativeHeatStep_chk_148_Gen :
    nativeHeatPassRootsOk nativeGap149Old nativeHeat148Frames nativeHeat148Coef nativeHeat148Fixed nativeHeat148Base 48 nativeHeat148Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_148_Gen : NativeHeatStepPassNum 148 := by
  refine nativeHeatStepPassNum_of_literals 148 nativeGap149Old nativeHeat148Frames (nativeHeatExpArg nativeGap149Old)
    nativeHeat148Exp nativeHeat148Coef nativeHeat148Fixed nativeHeat148Init nativeHeat148Base nativeHeatStep_hOld_148_Gen
    nativeHeatStep_hFr_148_Gen nativeHeatStep_hArg_148_Gen nativeHeatStep_hExp_148_Gen
    nativeHeatStep_hCoef_148_Gen nativeHeatStep_hFixed_148_Gen
    nativeHeatStep_hInit_148_Gen nativeHeatStep_hBase_148_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_148_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_148_Gen :
    nativeHeatY0Gen 148 = nativeShiftedFrame 1 (min nativeGap149Old.x nativeGap149Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_148_Gen, nativeHeatStep_hInd_148_Gen]

theorem nativeHeatStepFrameNum_148_Gen : NativeHeatStepFrameNum 148 := by
  have h1 := nativeHeatStep_hOld_148_Gen
  have h2 := nativeHeatStep_hInd_148_Gen
  have h3 := nativeHeatStep_hVar_148_Gen
  have h4 := nativeHeatStep_hQm_148_Gen
  have h5 := nativeHeatStep_hQN_148_Gen
  have h6 := nativeHeatStep_hY0_148_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_148_Gen : NativeHeatStepIndivNum 148 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 148 (by norm_num)) = nativeGap149Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_148_Gen]; exact nativeGap149Old_source
  · rw [hc, nativeHeatStep_hInd_148_Gen]; exact nativeGap149Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_148_Gen : nativeHeatY48Gen 148 = nativeHeat148Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_148_Gen, nativeHeatStep_hFr_148_Gen,
    nativeHeatStep_hCoef_148_Gen, nativeHeatStep_hFixed_148_Gen,
    nativeHeatStep_hBase_148_Gen]
  exact nativeHeat148All48

theorem nativeHeatResultGen_148 : nativeHeatResultGen 148 = nativeHeat148Result := by
  rw [← nativeHeat148Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_148_Gen, nativeHeatStep_hY0_148_Gen, nativeHeatStep_hExp_148_Gen,
    nativeHeatStep_hInit_148_Gen, nativeHeatStep_hFixed_148_Gen]

end ASDExplicitGamma.Native

end
