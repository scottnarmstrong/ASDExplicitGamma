module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat150Complete
public import ASDExplicitGamma.Numerics.Native.Gap151Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_150_Gen : nativeHeatOldRowGen 150 = nativeGap151Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_150_Gen : nativeHeatIndividualGen 150 = nativeGap151Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_150_Gen : nativeHeatGenVariance 150 = nativeHeat150Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_150_Gen, nativeHeat150Variance_formula]

theorem nativeHeatStep_hSpec_150_Gen : nativeHeatGenSpectral 150 = nativeHeat150Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_150_Gen, nativeHeat150Variance_formula]

theorem nativeHeatStep_hQm_150_Gen : nativeHeatGenQm 150 = nativeHeat150Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_150_Gen, nativeHeatStep_hSpec_150_Gen,
    nativeHeat150Qm_formula]

theorem nativeHeatStep_hQN_150_Gen : nativeHeatQNGen 150 = nativeHeat150QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_150_Gen, nativeHeat150QN_formula]

theorem nativeHeatStep_hFr_150_Gen : nativeHeatFramesGen 150 = nativeHeat150Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_150_Gen, nativeHeatStep_hInd_150_Gen,
    nativeHeatStep_hVar_150_Gen, nativeHeatStep_hQN_150_Gen, nativeHeat150Frames_formula]

theorem nativeHeatStep_hArg_150_Gen : nativeHeatExpArgGen 150 = nativeHeatExpArg nativeGap151Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_150_Gen]

theorem nativeHeatStep_hExp_150_Gen : nativeHeatExpGen 150 = nativeHeat150Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_150_Gen, nativeHeat150Exp_formula]

theorem nativeHeatStep_hCoef_150_Gen : nativeHeatCoefGen 150 = nativeHeat150Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_150_Gen, nativeHeat150Coef_formula]

theorem nativeHeatStep_hInit_150_Gen : nativeHeatInitGen 150 = nativeHeat150Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_150_Gen, nativeHeatStep_hVar_150_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat150Init00_formula
    · exact nativeHeat150Init01_formula
    · exact nativeHeat150Init02_formula
    · exact nativeHeat150Init03_formula
    · exact nativeHeat150Init04_formula
    · exact nativeHeat150Init05_formula
    · exact nativeHeat150Init06_formula
    · exact nativeHeat150Init07_formula
    · exact nativeHeat150Init08_formula
    · exact nativeHeat150Init09_formula
    · exact nativeHeat150Init10_formula
    · exact nativeHeat150Init11_formula
    · exact nativeHeat150Init12_formula
    · exact nativeHeat150Init13_formula
    · exact nativeHeat150Init14_formula
    · exact nativeHeat150Init15_formula
    · exact nativeHeat150Init16_formula
    · exact nativeHeat150Init17_formula
    · exact nativeHeat150Init18_formula
    · exact nativeHeat150Init19_formula
    · exact nativeHeat150Init20_formula
theorem nativeHeatStep_hBase_150_Gen : nativeHeatBaseGen 150 = nativeHeat150Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_150_Gen, nativeHeatStep_hInit_150_Gen, nativeHeat150Base_formula]

theorem nativeHeatStep_hFixed_150_Gen : nativeHeatFixedGen 150 = nativeHeat150Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_150_Gen, nativeHeatStep_hFr_150_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat150Fixed01_formula
    · exact nativeHeat150Fixed02_formula
    · exact nativeHeat150Fixed03_formula
    · exact nativeHeat150Fixed04_formula
    · exact nativeHeat150Fixed05_formula
    · exact nativeHeat150Fixed06_formula
    · exact nativeHeat150Fixed07_formula
    · exact nativeHeat150Fixed08_formula
    · exact nativeHeat150Fixed09_formula
    · exact nativeHeat150Fixed10_formula
    · exact nativeHeat150Fixed11_formula
    · exact nativeHeat150Fixed12_formula
    · exact nativeHeat150Fixed13_formula
    · exact nativeHeat150Fixed14_formula
    · exact nativeHeat150Fixed15_formula
    · exact nativeHeat150Fixed16_formula
    · exact nativeHeat150Fixed17_formula
    · exact nativeHeat150Fixed18_formula
    · exact nativeHeat150Fixed19_formula
    · exact nativeHeat150Fixed20_formula

theorem nativeHeatStep_chk_150_Gen :
    nativeHeatPassRootsOk nativeGap151Old nativeHeat150Frames nativeHeat150Coef nativeHeat150Fixed nativeHeat150Base 48 nativeHeat150Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_150_Gen : NativeHeatStepPassNum 150 := by
  refine nativeHeatStepPassNum_of_literals 150 nativeGap151Old nativeHeat150Frames (nativeHeatExpArg nativeGap151Old)
    nativeHeat150Exp nativeHeat150Coef nativeHeat150Fixed nativeHeat150Init nativeHeat150Base nativeHeatStep_hOld_150_Gen
    nativeHeatStep_hFr_150_Gen nativeHeatStep_hArg_150_Gen nativeHeatStep_hExp_150_Gen
    nativeHeatStep_hCoef_150_Gen nativeHeatStep_hFixed_150_Gen
    nativeHeatStep_hInit_150_Gen nativeHeatStep_hBase_150_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_150_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_150_Gen :
    nativeHeatY0Gen 150 = nativeShiftedFrame 1 (min nativeGap151Old.x nativeGap151Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_150_Gen, nativeHeatStep_hInd_150_Gen]

theorem nativeHeatStepFrameNum_150_Gen : NativeHeatStepFrameNum 150 := by
  have h1 := nativeHeatStep_hOld_150_Gen
  have h2 := nativeHeatStep_hInd_150_Gen
  have h3 := nativeHeatStep_hVar_150_Gen
  have h4 := nativeHeatStep_hQm_150_Gen
  have h5 := nativeHeatStep_hQN_150_Gen
  have h6 := nativeHeatStep_hY0_150_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_150_Gen : NativeHeatStepIndivNum 150 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 150 (by norm_num)) = nativeGap151Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_150_Gen]; exact nativeGap151Old_source
  · rw [hc, nativeHeatStep_hInd_150_Gen]; exact nativeGap151Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_150_Gen : nativeHeatY48Gen 150 = nativeHeat150Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_150_Gen, nativeHeatStep_hFr_150_Gen,
    nativeHeatStep_hCoef_150_Gen, nativeHeatStep_hFixed_150_Gen,
    nativeHeatStep_hBase_150_Gen]
  exact nativeHeat150All48

theorem nativeHeatResultGen_150 : nativeHeatResultGen 150 = nativeHeat150Result := by
  rw [← nativeHeat150Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_150_Gen, nativeHeatStep_hY0_150_Gen, nativeHeatStep_hExp_150_Gen,
    nativeHeatStep_hInit_150_Gen, nativeHeatStep_hFixed_150_Gen]

end ASDExplicitGamma.Native

end
