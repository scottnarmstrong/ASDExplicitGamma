module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat120Complete
public import ASDExplicitGamma.Numerics.Native.Gap121Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_120_Gen : nativeHeatOldRowGen 120 = nativeGap121Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_120_Gen : nativeHeatIndividualGen 120 = nativeGap121Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_120_Gen : nativeHeatGenVariance 120 = nativeHeat120Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_120_Gen, nativeHeat120Variance_formula]

theorem nativeHeatStep_hSpec_120_Gen : nativeHeatGenSpectral 120 = nativeHeat120Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_120_Gen, nativeHeat120Variance_formula]

theorem nativeHeatStep_hQm_120_Gen : nativeHeatGenQm 120 = nativeHeat120Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_120_Gen, nativeHeatStep_hSpec_120_Gen,
    nativeHeat120Qm_formula]

theorem nativeHeatStep_hQN_120_Gen : nativeHeatQNGen 120 = nativeHeat120QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_120_Gen, nativeHeat120QN_formula]

theorem nativeHeatStep_hFr_120_Gen : nativeHeatFramesGen 120 = nativeHeat120Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_120_Gen, nativeHeatStep_hInd_120_Gen,
    nativeHeatStep_hVar_120_Gen, nativeHeatStep_hQN_120_Gen, nativeHeat120Frames_formula]

theorem nativeHeatStep_hArg_120_Gen : nativeHeatExpArgGen 120 = nativeHeatExpArg nativeGap121Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_120_Gen]

theorem nativeHeatStep_hExp_120_Gen : nativeHeatExpGen 120 = nativeHeat120Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_120_Gen, nativeHeat120Exp_formula]

theorem nativeHeatStep_hCoef_120_Gen : nativeHeatCoefGen 120 = nativeHeat120Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_120_Gen, nativeHeat120Coef_formula]

theorem nativeHeatStep_hInit_120_Gen : nativeHeatInitGen 120 = nativeHeat120Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_120_Gen, nativeHeatStep_hVar_120_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat120Init00_formula
    · exact nativeHeat120Init01_formula
    · exact nativeHeat120Init02_formula
    · exact nativeHeat120Init03_formula
    · exact nativeHeat120Init04_formula
    · exact nativeHeat120Init05_formula
    · exact nativeHeat120Init06_formula
    · exact nativeHeat120Init07_formula
    · exact nativeHeat120Init08_formula
    · exact nativeHeat120Init09_formula
    · exact nativeHeat120Init10_formula
    · exact nativeHeat120Init11_formula
    · exact nativeHeat120Init12_formula
    · exact nativeHeat120Init13_formula
    · exact nativeHeat120Init14_formula
    · exact nativeHeat120Init15_formula
    · exact nativeHeat120Init16_formula
    · exact nativeHeat120Init17_formula
    · exact nativeHeat120Init18_formula
    · exact nativeHeat120Init19_formula
    · exact nativeHeat120Init20_formula
theorem nativeHeatStep_hBase_120_Gen : nativeHeatBaseGen 120 = nativeHeat120Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_120_Gen, nativeHeatStep_hInit_120_Gen, nativeHeat120Base_formula]

theorem nativeHeatStep_hFixed_120_Gen : nativeHeatFixedGen 120 = nativeHeat120Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_120_Gen, nativeHeatStep_hFr_120_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat120Fixed01_formula
    · exact nativeHeat120Fixed02_formula
    · exact nativeHeat120Fixed03_formula
    · exact nativeHeat120Fixed04_formula
    · exact nativeHeat120Fixed05_formula
    · exact nativeHeat120Fixed06_formula
    · exact nativeHeat120Fixed07_formula
    · exact nativeHeat120Fixed08_formula
    · exact nativeHeat120Fixed09_formula
    · exact nativeHeat120Fixed10_formula
    · exact nativeHeat120Fixed11_formula
    · exact nativeHeat120Fixed12_formula
    · exact nativeHeat120Fixed13_formula
    · exact nativeHeat120Fixed14_formula
    · exact nativeHeat120Fixed15_formula
    · exact nativeHeat120Fixed16_formula
    · exact nativeHeat120Fixed17_formula
    · exact nativeHeat120Fixed18_formula
    · exact nativeHeat120Fixed19_formula
    · exact nativeHeat120Fixed20_formula

theorem nativeHeatStep_chk_120_Gen :
    nativeHeatPassRootsOk nativeGap121Old nativeHeat120Frames nativeHeat120Coef nativeHeat120Fixed nativeHeat120Base 48 nativeHeat120Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_120_Gen : NativeHeatStepPassNum 120 := by
  refine nativeHeatStepPassNum_of_literals 120 nativeGap121Old nativeHeat120Frames (nativeHeatExpArg nativeGap121Old)
    nativeHeat120Exp nativeHeat120Coef nativeHeat120Fixed nativeHeat120Init nativeHeat120Base nativeHeatStep_hOld_120_Gen
    nativeHeatStep_hFr_120_Gen nativeHeatStep_hArg_120_Gen nativeHeatStep_hExp_120_Gen
    nativeHeatStep_hCoef_120_Gen nativeHeatStep_hFixed_120_Gen
    nativeHeatStep_hInit_120_Gen nativeHeatStep_hBase_120_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_120_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_120_Gen :
    nativeHeatY0Gen 120 = nativeShiftedFrame 1 (min nativeGap121Old.x nativeGap121Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_120_Gen, nativeHeatStep_hInd_120_Gen]

theorem nativeHeatStepFrameNum_120_Gen : NativeHeatStepFrameNum 120 := by
  have h1 := nativeHeatStep_hOld_120_Gen
  have h2 := nativeHeatStep_hInd_120_Gen
  have h3 := nativeHeatStep_hVar_120_Gen
  have h4 := nativeHeatStep_hQm_120_Gen
  have h5 := nativeHeatStep_hQN_120_Gen
  have h6 := nativeHeatStep_hY0_120_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_120_Gen : NativeHeatStepIndivNum 120 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 120 (by norm_num)) = nativeGap121Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_120_Gen]; exact nativeGap121Old_source
  · rw [hc, nativeHeatStep_hInd_120_Gen]; exact nativeGap121Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_120_Gen : nativeHeatY48Gen 120 = nativeHeat120Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_120_Gen, nativeHeatStep_hFr_120_Gen,
    nativeHeatStep_hCoef_120_Gen, nativeHeatStep_hFixed_120_Gen,
    nativeHeatStep_hBase_120_Gen]
  exact nativeHeat120All48

theorem nativeHeatResultGen_120 : nativeHeatResultGen 120 = nativeHeat120Result := by
  rw [← nativeHeat120Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_120_Gen, nativeHeatStep_hY0_120_Gen, nativeHeatStep_hExp_120_Gen,
    nativeHeatStep_hInit_120_Gen, nativeHeatStep_hFixed_120_Gen]

end ASDExplicitGamma.Native

end
