module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat074Complete
public import ASDExplicitGamma.Numerics.Native.Gap075Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_074_Gen : nativeHeatOldRowGen 74 = nativeGap075Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_074_Gen : nativeHeatIndividualGen 74 = nativeGap075Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_074_Gen : nativeHeatGenVariance 74 = nativeHeat074Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_074_Gen, nativeHeat074Variance_formula]

theorem nativeHeatStep_hSpec_074_Gen : nativeHeatGenSpectral 74 = nativeHeat074Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_074_Gen, nativeHeat074Variance_formula]

theorem nativeHeatStep_hQm_074_Gen : nativeHeatGenQm 74 = nativeHeat074Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_074_Gen, nativeHeatStep_hSpec_074_Gen,
    nativeHeat074Qm_formula]

theorem nativeHeatStep_hQN_074_Gen : nativeHeatQNGen 74 = nativeHeat074QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_074_Gen, nativeHeat074QN_formula]

theorem nativeHeatStep_hFr_074_Gen : nativeHeatFramesGen 74 = nativeHeat074Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_074_Gen, nativeHeatStep_hInd_074_Gen,
    nativeHeatStep_hVar_074_Gen, nativeHeatStep_hQN_074_Gen, nativeHeat074Frames_formula]

theorem nativeHeatStep_hArg_074_Gen : nativeHeatExpArgGen 74 = nativeHeatExpArg nativeGap075Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_074_Gen]

theorem nativeHeatStep_hExp_074_Gen : nativeHeatExpGen 74 = nativeHeat074Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_074_Gen, nativeHeat074Exp_formula]

theorem nativeHeatStep_hCoef_074_Gen : nativeHeatCoefGen 74 = nativeHeat074Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_074_Gen, nativeHeat074Coef_formula]

theorem nativeHeatStep_hInit_074_Gen : nativeHeatInitGen 74 = nativeHeat074Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_074_Gen, nativeHeatStep_hVar_074_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat074Init00_formula
    · exact nativeHeat074Init01_formula
    · exact nativeHeat074Init02_formula
    · exact nativeHeat074Init03_formula
    · exact nativeHeat074Init04_formula
    · exact nativeHeat074Init05_formula
    · exact nativeHeat074Init06_formula
    · exact nativeHeat074Init07_formula
    · exact nativeHeat074Init08_formula
    · exact nativeHeat074Init09_formula
    · exact nativeHeat074Init10_formula
    · exact nativeHeat074Init11_formula
    · exact nativeHeat074Init12_formula
    · exact nativeHeat074Init13_formula
    · exact nativeHeat074Init14_formula
    · exact nativeHeat074Init15_formula
    · exact nativeHeat074Init16_formula
    · exact nativeHeat074Init17_formula
    · exact nativeHeat074Init18_formula
    · exact nativeHeat074Init19_formula
    · exact nativeHeat074Init20_formula
theorem nativeHeatStep_hBase_074_Gen : nativeHeatBaseGen 74 = nativeHeat074Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_074_Gen, nativeHeatStep_hInit_074_Gen, nativeHeat074Base_formula]

theorem nativeHeatStep_hFixed_074_Gen : nativeHeatFixedGen 74 = nativeHeat074Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_074_Gen, nativeHeatStep_hFr_074_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat074Fixed01_formula
    · exact nativeHeat074Fixed02_formula
    · exact nativeHeat074Fixed03_formula
    · exact nativeHeat074Fixed04_formula
    · exact nativeHeat074Fixed05_formula
    · exact nativeHeat074Fixed06_formula
    · exact nativeHeat074Fixed07_formula
    · exact nativeHeat074Fixed08_formula
    · exact nativeHeat074Fixed09_formula
    · exact nativeHeat074Fixed10_formula
    · exact nativeHeat074Fixed11_formula
    · exact nativeHeat074Fixed12_formula
    · exact nativeHeat074Fixed13_formula
    · exact nativeHeat074Fixed14_formula
    · exact nativeHeat074Fixed15_formula
    · exact nativeHeat074Fixed16_formula
    · exact nativeHeat074Fixed17_formula
    · exact nativeHeat074Fixed18_formula
    · exact nativeHeat074Fixed19_formula
    · exact nativeHeat074Fixed20_formula

theorem nativeHeatStep_chk_074_Gen :
    nativeHeatPassRootsOk nativeGap075Old nativeHeat074Frames nativeHeat074Coef nativeHeat074Fixed nativeHeat074Base 48 nativeHeat074Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_074_Gen : NativeHeatStepPassNum 74 := by
  refine nativeHeatStepPassNum_of_literals 74 nativeGap075Old nativeHeat074Frames (nativeHeatExpArg nativeGap075Old)
    nativeHeat074Exp nativeHeat074Coef nativeHeat074Fixed nativeHeat074Init nativeHeat074Base nativeHeatStep_hOld_074_Gen
    nativeHeatStep_hFr_074_Gen nativeHeatStep_hArg_074_Gen nativeHeatStep_hExp_074_Gen
    nativeHeatStep_hCoef_074_Gen nativeHeatStep_hFixed_074_Gen
    nativeHeatStep_hInit_074_Gen nativeHeatStep_hBase_074_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_074_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_074_Gen :
    nativeHeatY0Gen 74 = nativeShiftedFrame 1 (min nativeGap075Old.x nativeGap075Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_074_Gen, nativeHeatStep_hInd_074_Gen]

theorem nativeHeatStepFrameNum_074_Gen : NativeHeatStepFrameNum 74 := by
  have h1 := nativeHeatStep_hOld_074_Gen
  have h2 := nativeHeatStep_hInd_074_Gen
  have h3 := nativeHeatStep_hVar_074_Gen
  have h4 := nativeHeatStep_hQm_074_Gen
  have h5 := nativeHeatStep_hQN_074_Gen
  have h6 := nativeHeatStep_hY0_074_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_074_Gen : NativeHeatStepIndivNum 74 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 74 (by norm_num)) = nativeGap075Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_074_Gen]; exact nativeGap075Old_source
  · rw [hc, nativeHeatStep_hInd_074_Gen]; exact nativeGap075Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_074_Gen : nativeHeatY48Gen 74 = nativeHeat074Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_074_Gen, nativeHeatStep_hFr_074_Gen,
    nativeHeatStep_hCoef_074_Gen, nativeHeatStep_hFixed_074_Gen,
    nativeHeatStep_hBase_074_Gen]
  exact nativeHeat074All48

theorem nativeHeatResultGen_074 : nativeHeatResultGen 74 = nativeHeat074Result := by
  rw [← nativeHeat074Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_074_Gen, nativeHeatStep_hY0_074_Gen, nativeHeatStep_hExp_074_Gen,
    nativeHeatStep_hInit_074_Gen, nativeHeatStep_hFixed_074_Gen]

end ASDExplicitGamma.Native

end
