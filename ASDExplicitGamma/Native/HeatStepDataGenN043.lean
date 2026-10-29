module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat043Complete
public import ASDExplicitGamma.Numerics.Native.Gap044Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_043_Gen : nativeHeatOldRowGen 43 = nativeGap044Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_043_Gen : nativeHeatIndividualGen 43 = nativeGap044Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_043_Gen : nativeHeatGenVariance 43 = nativeHeat043Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_043_Gen, nativeHeat043Variance_formula]

theorem nativeHeatStep_hSpec_043_Gen : nativeHeatGenSpectral 43 = nativeHeat043Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_043_Gen, nativeHeat043Variance_formula]

theorem nativeHeatStep_hQm_043_Gen : nativeHeatGenQm 43 = nativeHeat043Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_043_Gen, nativeHeatStep_hSpec_043_Gen,
    nativeHeat043Qm_formula]

theorem nativeHeatStep_hQN_043_Gen : nativeHeatQNGen 43 = nativeHeat043QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_043_Gen, nativeHeat043QN_formula]

theorem nativeHeatStep_hFr_043_Gen : nativeHeatFramesGen 43 = nativeHeat043Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_043_Gen, nativeHeatStep_hInd_043_Gen,
    nativeHeatStep_hVar_043_Gen, nativeHeatStep_hQN_043_Gen, nativeHeat043Frames_formula]

theorem nativeHeatStep_hArg_043_Gen : nativeHeatExpArgGen 43 = nativeHeatExpArg nativeGap044Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_043_Gen]

theorem nativeHeatStep_hExp_043_Gen : nativeHeatExpGen 43 = nativeHeat043Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_043_Gen, nativeHeat043Exp_formula]

theorem nativeHeatStep_hCoef_043_Gen : nativeHeatCoefGen 43 = nativeHeat043Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_043_Gen, nativeHeat043Coef_formula]

theorem nativeHeatStep_hInit_043_Gen : nativeHeatInitGen 43 = nativeHeat043Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_043_Gen, nativeHeatStep_hVar_043_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat043Init00_formula
    · exact nativeHeat043Init01_formula
    · exact nativeHeat043Init02_formula
    · exact nativeHeat043Init03_formula
    · exact nativeHeat043Init04_formula
    · exact nativeHeat043Init05_formula
    · exact nativeHeat043Init06_formula
    · exact nativeHeat043Init07_formula
    · exact nativeHeat043Init08_formula
    · exact nativeHeat043Init09_formula
    · exact nativeHeat043Init10_formula
    · exact nativeHeat043Init11_formula
    · exact nativeHeat043Init12_formula
    · exact nativeHeat043Init13_formula
    · exact nativeHeat043Init14_formula
    · exact nativeHeat043Init15_formula
    · exact nativeHeat043Init16_formula
    · exact nativeHeat043Init17_formula
    · exact nativeHeat043Init18_formula
    · exact nativeHeat043Init19_formula
    · exact nativeHeat043Init20_formula
theorem nativeHeatStep_hBase_043_Gen : nativeHeatBaseGen 43 = nativeHeat043Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_043_Gen, nativeHeatStep_hInit_043_Gen, nativeHeat043Base_formula]

theorem nativeHeatStep_hFixed_043_Gen : nativeHeatFixedGen 43 = nativeHeat043Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_043_Gen, nativeHeatStep_hFr_043_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat043Fixed01_formula
    · exact nativeHeat043Fixed02_formula
    · exact nativeHeat043Fixed03_formula
    · exact nativeHeat043Fixed04_formula
    · exact nativeHeat043Fixed05_formula
    · exact nativeHeat043Fixed06_formula
    · exact nativeHeat043Fixed07_formula
    · exact nativeHeat043Fixed08_formula
    · exact nativeHeat043Fixed09_formula
    · exact nativeHeat043Fixed10_formula
    · exact nativeHeat043Fixed11_formula
    · exact nativeHeat043Fixed12_formula
    · exact nativeHeat043Fixed13_formula
    · exact nativeHeat043Fixed14_formula
    · exact nativeHeat043Fixed15_formula
    · exact nativeHeat043Fixed16_formula
    · exact nativeHeat043Fixed17_formula
    · exact nativeHeat043Fixed18_formula
    · exact nativeHeat043Fixed19_formula
    · exact nativeHeat043Fixed20_formula

theorem nativeHeatStep_chk_043_Gen :
    nativeHeatPassRootsOk nativeGap044Old nativeHeat043Frames nativeHeat043Coef nativeHeat043Fixed nativeHeat043Base 48 nativeHeat043Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_043_Gen : NativeHeatStepPassNum 43 := by
  refine nativeHeatStepPassNum_of_literals 43 nativeGap044Old nativeHeat043Frames (nativeHeatExpArg nativeGap044Old)
    nativeHeat043Exp nativeHeat043Coef nativeHeat043Fixed nativeHeat043Init nativeHeat043Base nativeHeatStep_hOld_043_Gen
    nativeHeatStep_hFr_043_Gen nativeHeatStep_hArg_043_Gen nativeHeatStep_hExp_043_Gen
    nativeHeatStep_hCoef_043_Gen nativeHeatStep_hFixed_043_Gen
    nativeHeatStep_hInit_043_Gen nativeHeatStep_hBase_043_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_043_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_043_Gen :
    nativeHeatY0Gen 43 = nativeShiftedFrame 1 (min nativeGap044Old.x nativeGap044Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_043_Gen, nativeHeatStep_hInd_043_Gen]

theorem nativeHeatStepFrameNum_043_Gen : NativeHeatStepFrameNum 43 := by
  have h1 := nativeHeatStep_hOld_043_Gen
  have h2 := nativeHeatStep_hInd_043_Gen
  have h3 := nativeHeatStep_hVar_043_Gen
  have h4 := nativeHeatStep_hQm_043_Gen
  have h5 := nativeHeatStep_hQN_043_Gen
  have h6 := nativeHeatStep_hY0_043_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_043_Gen : NativeHeatStepIndivNum 43 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 43 (by norm_num)) = nativeGap044Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_043_Gen]; exact nativeGap044Old_source
  · rw [hc, nativeHeatStep_hInd_043_Gen]; exact nativeGap044Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_043_Gen : nativeHeatY48Gen 43 = nativeHeat043Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_043_Gen, nativeHeatStep_hFr_043_Gen,
    nativeHeatStep_hCoef_043_Gen, nativeHeatStep_hFixed_043_Gen,
    nativeHeatStep_hBase_043_Gen]
  exact nativeHeat043All48

theorem nativeHeatResultGen_043 : nativeHeatResultGen 43 = nativeHeat043Result := by
  rw [← nativeHeat043Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_043_Gen, nativeHeatStep_hY0_043_Gen, nativeHeatStep_hExp_043_Gen,
    nativeHeatStep_hInit_043_Gen, nativeHeatStep_hFixed_043_Gen]

end ASDExplicitGamma.Native

end
