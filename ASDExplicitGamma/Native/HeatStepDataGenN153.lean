module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat153Complete
public import ASDExplicitGamma.Numerics.Native.Gap154Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_153_Gen : nativeHeatOldRowGen 153 = nativeGap154Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_153_Gen : nativeHeatIndividualGen 153 = nativeGap154Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_153_Gen : nativeHeatGenVariance 153 = nativeHeat153Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_153_Gen, nativeHeat153Variance_formula]

theorem nativeHeatStep_hSpec_153_Gen : nativeHeatGenSpectral 153 = nativeHeat153Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_153_Gen, nativeHeat153Variance_formula]

theorem nativeHeatStep_hQm_153_Gen : nativeHeatGenQm 153 = nativeHeat153Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_153_Gen, nativeHeatStep_hSpec_153_Gen,
    nativeHeat153Qm_formula]

theorem nativeHeatStep_hQN_153_Gen : nativeHeatQNGen 153 = nativeHeat153QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_153_Gen, nativeHeat153QN_formula]

theorem nativeHeatStep_hFr_153_Gen : nativeHeatFramesGen 153 = nativeHeat153Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_153_Gen, nativeHeatStep_hInd_153_Gen,
    nativeHeatStep_hVar_153_Gen, nativeHeatStep_hQN_153_Gen, nativeHeat153Frames_formula]

theorem nativeHeatStep_hArg_153_Gen : nativeHeatExpArgGen 153 = nativeHeatExpArg nativeGap154Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_153_Gen]

theorem nativeHeatStep_hExp_153_Gen : nativeHeatExpGen 153 = nativeHeat153Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_153_Gen, nativeHeat153Exp_formula]

theorem nativeHeatStep_hCoef_153_Gen : nativeHeatCoefGen 153 = nativeHeat153Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_153_Gen, nativeHeat153Coef_formula]

theorem nativeHeatStep_hInit_153_Gen : nativeHeatInitGen 153 = nativeHeat153Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_153_Gen, nativeHeatStep_hVar_153_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat153Init00_formula
    · exact nativeHeat153Init01_formula
    · exact nativeHeat153Init02_formula
    · exact nativeHeat153Init03_formula
    · exact nativeHeat153Init04_formula
    · exact nativeHeat153Init05_formula
    · exact nativeHeat153Init06_formula
    · exact nativeHeat153Init07_formula
    · exact nativeHeat153Init08_formula
    · exact nativeHeat153Init09_formula
    · exact nativeHeat153Init10_formula
    · exact nativeHeat153Init11_formula
    · exact nativeHeat153Init12_formula
    · exact nativeHeat153Init13_formula
    · exact nativeHeat153Init14_formula
    · exact nativeHeat153Init15_formula
    · exact nativeHeat153Init16_formula
    · exact nativeHeat153Init17_formula
    · exact nativeHeat153Init18_formula
    · exact nativeHeat153Init19_formula
    · exact nativeHeat153Init20_formula
theorem nativeHeatStep_hBase_153_Gen : nativeHeatBaseGen 153 = nativeHeat153Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_153_Gen, nativeHeatStep_hInit_153_Gen, nativeHeat153Base_formula]

theorem nativeHeatStep_hFixed_153_Gen : nativeHeatFixedGen 153 = nativeHeat153Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_153_Gen, nativeHeatStep_hFr_153_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat153Fixed01_formula
    · exact nativeHeat153Fixed02_formula
    · exact nativeHeat153Fixed03_formula
    · exact nativeHeat153Fixed04_formula
    · exact nativeHeat153Fixed05_formula
    · exact nativeHeat153Fixed06_formula
    · exact nativeHeat153Fixed07_formula
    · exact nativeHeat153Fixed08_formula
    · exact nativeHeat153Fixed09_formula
    · exact nativeHeat153Fixed10_formula
    · exact nativeHeat153Fixed11_formula
    · exact nativeHeat153Fixed12_formula
    · exact nativeHeat153Fixed13_formula
    · exact nativeHeat153Fixed14_formula
    · exact nativeHeat153Fixed15_formula
    · exact nativeHeat153Fixed16_formula
    · exact nativeHeat153Fixed17_formula
    · exact nativeHeat153Fixed18_formula
    · exact nativeHeat153Fixed19_formula
    · exact nativeHeat153Fixed20_formula

theorem nativeHeatStep_chk_153_Gen :
    nativeHeatPassRootsOk nativeGap154Old nativeHeat153Frames nativeHeat153Coef nativeHeat153Fixed nativeHeat153Base 48 nativeHeat153Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_153_Gen : NativeHeatStepPassNum 153 := by
  refine nativeHeatStepPassNum_of_literals 153 nativeGap154Old nativeHeat153Frames (nativeHeatExpArg nativeGap154Old)
    nativeHeat153Exp nativeHeat153Coef nativeHeat153Fixed nativeHeat153Init nativeHeat153Base nativeHeatStep_hOld_153_Gen
    nativeHeatStep_hFr_153_Gen nativeHeatStep_hArg_153_Gen nativeHeatStep_hExp_153_Gen
    nativeHeatStep_hCoef_153_Gen nativeHeatStep_hFixed_153_Gen
    nativeHeatStep_hInit_153_Gen nativeHeatStep_hBase_153_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_153_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_153_Gen :
    nativeHeatY0Gen 153 = nativeShiftedFrame 1 (min nativeGap154Old.x nativeGap154Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_153_Gen, nativeHeatStep_hInd_153_Gen]

theorem nativeHeatStepFrameNum_153_Gen : NativeHeatStepFrameNum 153 := by
  have h1 := nativeHeatStep_hOld_153_Gen
  have h2 := nativeHeatStep_hInd_153_Gen
  have h3 := nativeHeatStep_hVar_153_Gen
  have h4 := nativeHeatStep_hQm_153_Gen
  have h5 := nativeHeatStep_hQN_153_Gen
  have h6 := nativeHeatStep_hY0_153_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_153_Gen : NativeHeatStepIndivNum 153 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 153 (by norm_num)) = nativeGap154Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_153_Gen]; exact nativeGap154Old_source
  · rw [hc, nativeHeatStep_hInd_153_Gen]; exact nativeGap154Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_153_Gen : nativeHeatY48Gen 153 = nativeHeat153Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_153_Gen, nativeHeatStep_hFr_153_Gen,
    nativeHeatStep_hCoef_153_Gen, nativeHeatStep_hFixed_153_Gen,
    nativeHeatStep_hBase_153_Gen]
  exact nativeHeat153All48

theorem nativeHeatResultGen_153 : nativeHeatResultGen 153 = nativeHeat153Result := by
  rw [← nativeHeat153Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_153_Gen, nativeHeatStep_hY0_153_Gen, nativeHeatStep_hExp_153_Gen,
    nativeHeatStep_hInit_153_Gen, nativeHeatStep_hFixed_153_Gen]

end ASDExplicitGamma.Native

end
