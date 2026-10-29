module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat045Complete
public import ASDExplicitGamma.Numerics.Native.Gap046Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_045_Gen : nativeHeatOldRowGen 45 = nativeGap046Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_045_Gen : nativeHeatIndividualGen 45 = nativeGap046Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_045_Gen : nativeHeatGenVariance 45 = nativeHeat045Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_045_Gen, nativeHeat045Variance_formula]

theorem nativeHeatStep_hSpec_045_Gen : nativeHeatGenSpectral 45 = nativeHeat045Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_045_Gen, nativeHeat045Variance_formula]

theorem nativeHeatStep_hQm_045_Gen : nativeHeatGenQm 45 = nativeHeat045Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_045_Gen, nativeHeatStep_hSpec_045_Gen,
    nativeHeat045Qm_formula]

theorem nativeHeatStep_hQN_045_Gen : nativeHeatQNGen 45 = nativeHeat045QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_045_Gen, nativeHeat045QN_formula]

theorem nativeHeatStep_hFr_045_Gen : nativeHeatFramesGen 45 = nativeHeat045Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_045_Gen, nativeHeatStep_hInd_045_Gen,
    nativeHeatStep_hVar_045_Gen, nativeHeatStep_hQN_045_Gen, nativeHeat045Frames_formula]

theorem nativeHeatStep_hArg_045_Gen : nativeHeatExpArgGen 45 = nativeHeatExpArg nativeGap046Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_045_Gen]

theorem nativeHeatStep_hExp_045_Gen : nativeHeatExpGen 45 = nativeHeat045Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_045_Gen, nativeHeat045Exp_formula]

theorem nativeHeatStep_hCoef_045_Gen : nativeHeatCoefGen 45 = nativeHeat045Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_045_Gen, nativeHeat045Coef_formula]

theorem nativeHeatStep_hInit_045_Gen : nativeHeatInitGen 45 = nativeHeat045Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_045_Gen, nativeHeatStep_hVar_045_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat045Init00_formula
    · exact nativeHeat045Init01_formula
    · exact nativeHeat045Init02_formula
    · exact nativeHeat045Init03_formula
    · exact nativeHeat045Init04_formula
    · exact nativeHeat045Init05_formula
    · exact nativeHeat045Init06_formula
    · exact nativeHeat045Init07_formula
    · exact nativeHeat045Init08_formula
    · exact nativeHeat045Init09_formula
    · exact nativeHeat045Init10_formula
    · exact nativeHeat045Init11_formula
    · exact nativeHeat045Init12_formula
    · exact nativeHeat045Init13_formula
    · exact nativeHeat045Init14_formula
    · exact nativeHeat045Init15_formula
    · exact nativeHeat045Init16_formula
    · exact nativeHeat045Init17_formula
    · exact nativeHeat045Init18_formula
    · exact nativeHeat045Init19_formula
    · exact nativeHeat045Init20_formula
theorem nativeHeatStep_hBase_045_Gen : nativeHeatBaseGen 45 = nativeHeat045Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_045_Gen, nativeHeatStep_hInit_045_Gen, nativeHeat045Base_formula]

theorem nativeHeatStep_hFixed_045_Gen : nativeHeatFixedGen 45 = nativeHeat045Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_045_Gen, nativeHeatStep_hFr_045_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat045Fixed01_formula
    · exact nativeHeat045Fixed02_formula
    · exact nativeHeat045Fixed03_formula
    · exact nativeHeat045Fixed04_formula
    · exact nativeHeat045Fixed05_formula
    · exact nativeHeat045Fixed06_formula
    · exact nativeHeat045Fixed07_formula
    · exact nativeHeat045Fixed08_formula
    · exact nativeHeat045Fixed09_formula
    · exact nativeHeat045Fixed10_formula
    · exact nativeHeat045Fixed11_formula
    · exact nativeHeat045Fixed12_formula
    · exact nativeHeat045Fixed13_formula
    · exact nativeHeat045Fixed14_formula
    · exact nativeHeat045Fixed15_formula
    · exact nativeHeat045Fixed16_formula
    · exact nativeHeat045Fixed17_formula
    · exact nativeHeat045Fixed18_formula
    · exact nativeHeat045Fixed19_formula
    · exact nativeHeat045Fixed20_formula

theorem nativeHeatStep_chk_045_Gen :
    nativeHeatPassRootsOk nativeGap046Old nativeHeat045Frames nativeHeat045Coef nativeHeat045Fixed nativeHeat045Base 48 nativeHeat045Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_045_Gen : NativeHeatStepPassNum 45 := by
  refine nativeHeatStepPassNum_of_literals 45 nativeGap046Old nativeHeat045Frames (nativeHeatExpArg nativeGap046Old)
    nativeHeat045Exp nativeHeat045Coef nativeHeat045Fixed nativeHeat045Init nativeHeat045Base nativeHeatStep_hOld_045_Gen
    nativeHeatStep_hFr_045_Gen nativeHeatStep_hArg_045_Gen nativeHeatStep_hExp_045_Gen
    nativeHeatStep_hCoef_045_Gen nativeHeatStep_hFixed_045_Gen
    nativeHeatStep_hInit_045_Gen nativeHeatStep_hBase_045_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_045_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_045_Gen :
    nativeHeatY0Gen 45 = nativeShiftedFrame 1 (min nativeGap046Old.x nativeGap046Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_045_Gen, nativeHeatStep_hInd_045_Gen]

theorem nativeHeatStepFrameNum_045_Gen : NativeHeatStepFrameNum 45 := by
  have h1 := nativeHeatStep_hOld_045_Gen
  have h2 := nativeHeatStep_hInd_045_Gen
  have h3 := nativeHeatStep_hVar_045_Gen
  have h4 := nativeHeatStep_hQm_045_Gen
  have h5 := nativeHeatStep_hQN_045_Gen
  have h6 := nativeHeatStep_hY0_045_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_045_Gen : NativeHeatStepIndivNum 45 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 45 (by norm_num)) = nativeGap046Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_045_Gen]; exact nativeGap046Old_source
  · rw [hc, nativeHeatStep_hInd_045_Gen]; exact nativeGap046Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_045_Gen : nativeHeatY48Gen 45 = nativeHeat045Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_045_Gen, nativeHeatStep_hFr_045_Gen,
    nativeHeatStep_hCoef_045_Gen, nativeHeatStep_hFixed_045_Gen,
    nativeHeatStep_hBase_045_Gen]
  exact nativeHeat045All48

theorem nativeHeatResultGen_045 : nativeHeatResultGen 45 = nativeHeat045Result := by
  rw [← nativeHeat045Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_045_Gen, nativeHeatStep_hY0_045_Gen, nativeHeatStep_hExp_045_Gen,
    nativeHeatStep_hInit_045_Gen, nativeHeatStep_hFixed_045_Gen]

end ASDExplicitGamma.Native

end
