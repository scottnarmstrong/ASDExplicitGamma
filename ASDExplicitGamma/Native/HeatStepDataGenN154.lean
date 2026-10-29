module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat154Complete
public import ASDExplicitGamma.Numerics.Native.Gap155Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_154_Gen : nativeHeatOldRowGen 154 = nativeGap155Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_154_Gen : nativeHeatIndividualGen 154 = nativeGap155Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_154_Gen : nativeHeatGenVariance 154 = nativeHeat154Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_154_Gen, nativeHeat154Variance_formula]

theorem nativeHeatStep_hSpec_154_Gen : nativeHeatGenSpectral 154 = nativeHeat154Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_154_Gen, nativeHeat154Variance_formula]

theorem nativeHeatStep_hQm_154_Gen : nativeHeatGenQm 154 = nativeHeat154Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_154_Gen, nativeHeatStep_hSpec_154_Gen,
    nativeHeat154Qm_formula]

theorem nativeHeatStep_hQN_154_Gen : nativeHeatQNGen 154 = nativeHeat154QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_154_Gen, nativeHeat154QN_formula]

theorem nativeHeatStep_hFr_154_Gen : nativeHeatFramesGen 154 = nativeHeat154Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_154_Gen, nativeHeatStep_hInd_154_Gen,
    nativeHeatStep_hVar_154_Gen, nativeHeatStep_hQN_154_Gen, nativeHeat154Frames_formula]

theorem nativeHeatStep_hArg_154_Gen : nativeHeatExpArgGen 154 = nativeHeatExpArg nativeGap155Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_154_Gen]

theorem nativeHeatStep_hExp_154_Gen : nativeHeatExpGen 154 = nativeHeat154Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_154_Gen, nativeHeat154Exp_formula]

theorem nativeHeatStep_hCoef_154_Gen : nativeHeatCoefGen 154 = nativeHeat154Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_154_Gen, nativeHeat154Coef_formula]

theorem nativeHeatStep_hInit_154_Gen : nativeHeatInitGen 154 = nativeHeat154Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_154_Gen, nativeHeatStep_hVar_154_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat154Init00_formula
    · exact nativeHeat154Init01_formula
    · exact nativeHeat154Init02_formula
    · exact nativeHeat154Init03_formula
    · exact nativeHeat154Init04_formula
    · exact nativeHeat154Init05_formula
    · exact nativeHeat154Init06_formula
    · exact nativeHeat154Init07_formula
    · exact nativeHeat154Init08_formula
    · exact nativeHeat154Init09_formula
    · exact nativeHeat154Init10_formula
    · exact nativeHeat154Init11_formula
    · exact nativeHeat154Init12_formula
    · exact nativeHeat154Init13_formula
    · exact nativeHeat154Init14_formula
    · exact nativeHeat154Init15_formula
    · exact nativeHeat154Init16_formula
    · exact nativeHeat154Init17_formula
    · exact nativeHeat154Init18_formula
    · exact nativeHeat154Init19_formula
    · exact nativeHeat154Init20_formula
theorem nativeHeatStep_hBase_154_Gen : nativeHeatBaseGen 154 = nativeHeat154Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_154_Gen, nativeHeatStep_hInit_154_Gen, nativeHeat154Base_formula]

theorem nativeHeatStep_hFixed_154_Gen : nativeHeatFixedGen 154 = nativeHeat154Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_154_Gen, nativeHeatStep_hFr_154_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat154Fixed01_formula
    · exact nativeHeat154Fixed02_formula
    · exact nativeHeat154Fixed03_formula
    · exact nativeHeat154Fixed04_formula
    · exact nativeHeat154Fixed05_formula
    · exact nativeHeat154Fixed06_formula
    · exact nativeHeat154Fixed07_formula
    · exact nativeHeat154Fixed08_formula
    · exact nativeHeat154Fixed09_formula
    · exact nativeHeat154Fixed10_formula
    · exact nativeHeat154Fixed11_formula
    · exact nativeHeat154Fixed12_formula
    · exact nativeHeat154Fixed13_formula
    · exact nativeHeat154Fixed14_formula
    · exact nativeHeat154Fixed15_formula
    · exact nativeHeat154Fixed16_formula
    · exact nativeHeat154Fixed17_formula
    · exact nativeHeat154Fixed18_formula
    · exact nativeHeat154Fixed19_formula
    · exact nativeHeat154Fixed20_formula

theorem nativeHeatStep_chk_154_Gen :
    nativeHeatPassRootsOk nativeGap155Old nativeHeat154Frames nativeHeat154Coef nativeHeat154Fixed nativeHeat154Base 48 nativeHeat154Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_154_Gen : NativeHeatStepPassNum 154 := by
  refine nativeHeatStepPassNum_of_literals 154 nativeGap155Old nativeHeat154Frames (nativeHeatExpArg nativeGap155Old)
    nativeHeat154Exp nativeHeat154Coef nativeHeat154Fixed nativeHeat154Init nativeHeat154Base nativeHeatStep_hOld_154_Gen
    nativeHeatStep_hFr_154_Gen nativeHeatStep_hArg_154_Gen nativeHeatStep_hExp_154_Gen
    nativeHeatStep_hCoef_154_Gen nativeHeatStep_hFixed_154_Gen
    nativeHeatStep_hInit_154_Gen nativeHeatStep_hBase_154_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_154_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_154_Gen :
    nativeHeatY0Gen 154 = nativeShiftedFrame 1 (min nativeGap155Old.x nativeGap155Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_154_Gen, nativeHeatStep_hInd_154_Gen]

theorem nativeHeatStepFrameNum_154_Gen : NativeHeatStepFrameNum 154 := by
  have h1 := nativeHeatStep_hOld_154_Gen
  have h2 := nativeHeatStep_hInd_154_Gen
  have h3 := nativeHeatStep_hVar_154_Gen
  have h4 := nativeHeatStep_hQm_154_Gen
  have h5 := nativeHeatStep_hQN_154_Gen
  have h6 := nativeHeatStep_hY0_154_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_154_Gen : NativeHeatStepIndivNum 154 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 154 (by norm_num)) = nativeGap155Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_154_Gen]; exact nativeGap155Old_source
  · rw [hc, nativeHeatStep_hInd_154_Gen]; exact nativeGap155Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_154_Gen : nativeHeatY48Gen 154 = nativeHeat154Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_154_Gen, nativeHeatStep_hFr_154_Gen,
    nativeHeatStep_hCoef_154_Gen, nativeHeatStep_hFixed_154_Gen,
    nativeHeatStep_hBase_154_Gen]
  exact nativeHeat154All48

theorem nativeHeatResultGen_154 : nativeHeatResultGen 154 = nativeHeat154Result := by
  rw [← nativeHeat154Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_154_Gen, nativeHeatStep_hY0_154_Gen, nativeHeatStep_hExp_154_Gen,
    nativeHeatStep_hInit_154_Gen, nativeHeatStep_hFixed_154_Gen]

end ASDExplicitGamma.Native

end
