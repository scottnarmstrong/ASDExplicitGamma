module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat119Complete
public import ASDExplicitGamma.Numerics.Native.Gap120Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_119_Gen : nativeHeatOldRowGen 119 = nativeGap120Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_119_Gen : nativeHeatIndividualGen 119 = nativeGap120Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_119_Gen : nativeHeatGenVariance 119 = nativeHeat119Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_119_Gen, nativeHeat119Variance_formula]

theorem nativeHeatStep_hSpec_119_Gen : nativeHeatGenSpectral 119 = nativeHeat119Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_119_Gen, nativeHeat119Variance_formula]

theorem nativeHeatStep_hQm_119_Gen : nativeHeatGenQm 119 = nativeHeat119Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_119_Gen, nativeHeatStep_hSpec_119_Gen,
    nativeHeat119Qm_formula]

theorem nativeHeatStep_hQN_119_Gen : nativeHeatQNGen 119 = nativeHeat119QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_119_Gen, nativeHeat119QN_formula]

theorem nativeHeatStep_hFr_119_Gen : nativeHeatFramesGen 119 = nativeHeat119Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_119_Gen, nativeHeatStep_hInd_119_Gen,
    nativeHeatStep_hVar_119_Gen, nativeHeatStep_hQN_119_Gen, nativeHeat119Frames_formula]

theorem nativeHeatStep_hArg_119_Gen : nativeHeatExpArgGen 119 = nativeHeatExpArg nativeGap120Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_119_Gen]

theorem nativeHeatStep_hExp_119_Gen : nativeHeatExpGen 119 = nativeHeat119Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_119_Gen, nativeHeat119Exp_formula]

theorem nativeHeatStep_hCoef_119_Gen : nativeHeatCoefGen 119 = nativeHeat119Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_119_Gen, nativeHeat119Coef_formula]

theorem nativeHeatStep_hInit_119_Gen : nativeHeatInitGen 119 = nativeHeat119Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_119_Gen, nativeHeatStep_hVar_119_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat119Init00_formula
    · exact nativeHeat119Init01_formula
    · exact nativeHeat119Init02_formula
    · exact nativeHeat119Init03_formula
    · exact nativeHeat119Init04_formula
    · exact nativeHeat119Init05_formula
    · exact nativeHeat119Init06_formula
    · exact nativeHeat119Init07_formula
    · exact nativeHeat119Init08_formula
    · exact nativeHeat119Init09_formula
    · exact nativeHeat119Init10_formula
    · exact nativeHeat119Init11_formula
    · exact nativeHeat119Init12_formula
    · exact nativeHeat119Init13_formula
    · exact nativeHeat119Init14_formula
    · exact nativeHeat119Init15_formula
    · exact nativeHeat119Init16_formula
    · exact nativeHeat119Init17_formula
    · exact nativeHeat119Init18_formula
    · exact nativeHeat119Init19_formula
    · exact nativeHeat119Init20_formula
theorem nativeHeatStep_hBase_119_Gen : nativeHeatBaseGen 119 = nativeHeat119Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_119_Gen, nativeHeatStep_hInit_119_Gen, nativeHeat119Base_formula]

theorem nativeHeatStep_hFixed_119_Gen : nativeHeatFixedGen 119 = nativeHeat119Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_119_Gen, nativeHeatStep_hFr_119_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat119Fixed01_formula
    · exact nativeHeat119Fixed02_formula
    · exact nativeHeat119Fixed03_formula
    · exact nativeHeat119Fixed04_formula
    · exact nativeHeat119Fixed05_formula
    · exact nativeHeat119Fixed06_formula
    · exact nativeHeat119Fixed07_formula
    · exact nativeHeat119Fixed08_formula
    · exact nativeHeat119Fixed09_formula
    · exact nativeHeat119Fixed10_formula
    · exact nativeHeat119Fixed11_formula
    · exact nativeHeat119Fixed12_formula
    · exact nativeHeat119Fixed13_formula
    · exact nativeHeat119Fixed14_formula
    · exact nativeHeat119Fixed15_formula
    · exact nativeHeat119Fixed16_formula
    · exact nativeHeat119Fixed17_formula
    · exact nativeHeat119Fixed18_formula
    · exact nativeHeat119Fixed19_formula
    · exact nativeHeat119Fixed20_formula

theorem nativeHeatStep_chk_119_Gen :
    nativeHeatPassRootsOk nativeGap120Old nativeHeat119Frames nativeHeat119Coef nativeHeat119Fixed nativeHeat119Base 48 nativeHeat119Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_119_Gen : NativeHeatStepPassNum 119 := by
  refine nativeHeatStepPassNum_of_literals 119 nativeGap120Old nativeHeat119Frames (nativeHeatExpArg nativeGap120Old)
    nativeHeat119Exp nativeHeat119Coef nativeHeat119Fixed nativeHeat119Init nativeHeat119Base nativeHeatStep_hOld_119_Gen
    nativeHeatStep_hFr_119_Gen nativeHeatStep_hArg_119_Gen nativeHeatStep_hExp_119_Gen
    nativeHeatStep_hCoef_119_Gen nativeHeatStep_hFixed_119_Gen
    nativeHeatStep_hInit_119_Gen nativeHeatStep_hBase_119_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_119_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_119_Gen :
    nativeHeatY0Gen 119 = nativeShiftedFrame 1 (min nativeGap120Old.x nativeGap120Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_119_Gen, nativeHeatStep_hInd_119_Gen]

theorem nativeHeatStepFrameNum_119_Gen : NativeHeatStepFrameNum 119 := by
  have h1 := nativeHeatStep_hOld_119_Gen
  have h2 := nativeHeatStep_hInd_119_Gen
  have h3 := nativeHeatStep_hVar_119_Gen
  have h4 := nativeHeatStep_hQm_119_Gen
  have h5 := nativeHeatStep_hQN_119_Gen
  have h6 := nativeHeatStep_hY0_119_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_119_Gen : NativeHeatStepIndivNum 119 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 119 (by norm_num)) = nativeGap120Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_119_Gen]; exact nativeGap120Old_source
  · rw [hc, nativeHeatStep_hInd_119_Gen]; exact nativeGap120Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_119_Gen : nativeHeatY48Gen 119 = nativeHeat119Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_119_Gen, nativeHeatStep_hFr_119_Gen,
    nativeHeatStep_hCoef_119_Gen, nativeHeatStep_hFixed_119_Gen,
    nativeHeatStep_hBase_119_Gen]
  exact nativeHeat119All48

theorem nativeHeatResultGen_119 : nativeHeatResultGen 119 = nativeHeat119Result := by
  rw [← nativeHeat119Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_119_Gen, nativeHeatStep_hY0_119_Gen, nativeHeatStep_hExp_119_Gen,
    nativeHeatStep_hInit_119_Gen, nativeHeatStep_hFixed_119_Gen]

end ASDExplicitGamma.Native

end
