module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat018Complete
public import ASDExplicitGamma.Numerics.Native.Gap019Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_018_Gen : nativeHeatOldRowGen 18 = nativeGap019Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_018_Gen : nativeHeatIndividualGen 18 = nativeGap019Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_018_Gen : nativeHeatGenVariance 18 = nativeHeat018Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_018_Gen, nativeHeat018Variance_formula]

theorem nativeHeatStep_hSpec_018_Gen : nativeHeatGenSpectral 18 = nativeHeat018Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_018_Gen, nativeHeat018Variance_formula]

theorem nativeHeatStep_hQm_018_Gen : nativeHeatGenQm 18 = nativeHeat018Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_018_Gen, nativeHeatStep_hSpec_018_Gen,
    nativeHeat018Qm_formula]

theorem nativeHeatStep_hQN_018_Gen : nativeHeatQNGen 18 = nativeHeat018QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_018_Gen, nativeHeat018QN_formula]

theorem nativeHeatStep_hFr_018_Gen : nativeHeatFramesGen 18 = nativeHeat018Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_018_Gen, nativeHeatStep_hInd_018_Gen,
    nativeHeatStep_hVar_018_Gen, nativeHeatStep_hQN_018_Gen, nativeHeat018Frames_formula]

theorem nativeHeatStep_hArg_018_Gen : nativeHeatExpArgGen 18 = nativeHeatExpArg nativeGap019Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_018_Gen]

theorem nativeHeatStep_hExp_018_Gen : nativeHeatExpGen 18 = nativeHeat018Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_018_Gen, nativeHeat018Exp_formula]

theorem nativeHeatStep_hCoef_018_Gen : nativeHeatCoefGen 18 = nativeHeat018Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_018_Gen, nativeHeat018Coef_formula]

theorem nativeHeatStep_hInit_018_Gen : nativeHeatInitGen 18 = nativeHeat018Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_018_Gen, nativeHeatStep_hVar_018_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat018Init00_formula
    · exact nativeHeat018Init01_formula
    · exact nativeHeat018Init02_formula
    · exact nativeHeat018Init03_formula
    · exact nativeHeat018Init04_formula
    · exact nativeHeat018Init05_formula
    · exact nativeHeat018Init06_formula
    · exact nativeHeat018Init07_formula
    · exact nativeHeat018Init08_formula
    · exact nativeHeat018Init09_formula
    · exact nativeHeat018Init10_formula
    · exact nativeHeat018Init11_formula
    · exact nativeHeat018Init12_formula
    · exact nativeHeat018Init13_formula
    · exact nativeHeat018Init14_formula
    · exact nativeHeat018Init15_formula
    · exact nativeHeat018Init16_formula
    · exact nativeHeat018Init17_formula
    · exact nativeHeat018Init18_formula
    · exact nativeHeat018Init19_formula
    · exact nativeHeat018Init20_formula
theorem nativeHeatStep_hBase_018_Gen : nativeHeatBaseGen 18 = nativeHeat018Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_018_Gen, nativeHeatStep_hInit_018_Gen, nativeHeat018Base_formula]

theorem nativeHeatStep_hFixed_018_Gen : nativeHeatFixedGen 18 = nativeHeat018Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_018_Gen, nativeHeatStep_hFr_018_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat018Fixed01_formula
    · exact nativeHeat018Fixed02_formula
    · exact nativeHeat018Fixed03_formula
    · exact nativeHeat018Fixed04_formula
    · exact nativeHeat018Fixed05_formula
    · exact nativeHeat018Fixed06_formula
    · exact nativeHeat018Fixed07_formula
    · exact nativeHeat018Fixed08_formula
    · exact nativeHeat018Fixed09_formula
    · exact nativeHeat018Fixed10_formula
    · exact nativeHeat018Fixed11_formula
    · exact nativeHeat018Fixed12_formula
    · exact nativeHeat018Fixed13_formula
    · exact nativeHeat018Fixed14_formula
    · exact nativeHeat018Fixed15_formula
    · exact nativeHeat018Fixed16_formula
    · exact nativeHeat018Fixed17_formula
    · exact nativeHeat018Fixed18_formula
    · exact nativeHeat018Fixed19_formula
    · exact nativeHeat018Fixed20_formula

theorem nativeHeatStep_chk_018_Gen :
    nativeHeatPassRootsOk nativeGap019Old nativeHeat018Frames nativeHeat018Coef nativeHeat018Fixed nativeHeat018Base 48 nativeHeat018Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_018_Gen : NativeHeatStepPassNum 18 := by
  refine nativeHeatStepPassNum_of_literals 18 nativeGap019Old nativeHeat018Frames (nativeHeatExpArg nativeGap019Old)
    nativeHeat018Exp nativeHeat018Coef nativeHeat018Fixed nativeHeat018Init nativeHeat018Base nativeHeatStep_hOld_018_Gen
    nativeHeatStep_hFr_018_Gen nativeHeatStep_hArg_018_Gen nativeHeatStep_hExp_018_Gen
    nativeHeatStep_hCoef_018_Gen nativeHeatStep_hFixed_018_Gen
    nativeHeatStep_hInit_018_Gen nativeHeatStep_hBase_018_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_018_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_018_Gen :
    nativeHeatY0Gen 18 = nativeShiftedFrame 1 (min nativeGap019Old.x nativeGap019Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_018_Gen, nativeHeatStep_hInd_018_Gen]

theorem nativeHeatStepFrameNum_018_Gen : NativeHeatStepFrameNum 18 := by
  have h1 := nativeHeatStep_hOld_018_Gen
  have h2 := nativeHeatStep_hInd_018_Gen
  have h3 := nativeHeatStep_hVar_018_Gen
  have h4 := nativeHeatStep_hQm_018_Gen
  have h5 := nativeHeatStep_hQN_018_Gen
  have h6 := nativeHeatStep_hY0_018_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_018_Gen : NativeHeatStepIndivNum 18 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 18 (by norm_num)) = nativeGap019Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_018_Gen]; exact nativeGap019Old_source
  · rw [hc, nativeHeatStep_hInd_018_Gen]; exact nativeGap019Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_018_Gen : nativeHeatY48Gen 18 = nativeHeat018Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_018_Gen, nativeHeatStep_hFr_018_Gen,
    nativeHeatStep_hCoef_018_Gen, nativeHeatStep_hFixed_018_Gen,
    nativeHeatStep_hBase_018_Gen]
  exact nativeHeat018All48

theorem nativeHeatResultGen_018 : nativeHeatResultGen 18 = nativeHeat018Result := by
  rw [← nativeHeat018Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_018_Gen, nativeHeatStep_hY0_018_Gen, nativeHeatStep_hExp_018_Gen,
    nativeHeatStep_hInit_018_Gen, nativeHeatStep_hFixed_018_Gen]

end ASDExplicitGamma.Native

end
