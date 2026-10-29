module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat028Complete
public import ASDExplicitGamma.Numerics.Native.Gap029Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_028_Gen : nativeHeatOldRowGen 28 = nativeGap029Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_028_Gen : nativeHeatIndividualGen 28 = nativeGap029Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_028_Gen : nativeHeatGenVariance 28 = nativeHeat028Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_028_Gen, nativeHeat028Variance_formula]

theorem nativeHeatStep_hSpec_028_Gen : nativeHeatGenSpectral 28 = nativeHeat028Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_028_Gen, nativeHeat028Variance_formula]

theorem nativeHeatStep_hQm_028_Gen : nativeHeatGenQm 28 = nativeHeat028Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_028_Gen, nativeHeatStep_hSpec_028_Gen,
    nativeHeat028Qm_formula]

theorem nativeHeatStep_hQN_028_Gen : nativeHeatQNGen 28 = nativeHeat028QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_028_Gen, nativeHeat028QN_formula]

theorem nativeHeatStep_hFr_028_Gen : nativeHeatFramesGen 28 = nativeHeat028Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_028_Gen, nativeHeatStep_hInd_028_Gen,
    nativeHeatStep_hVar_028_Gen, nativeHeatStep_hQN_028_Gen, nativeHeat028Frames_formula]

theorem nativeHeatStep_hArg_028_Gen : nativeHeatExpArgGen 28 = nativeHeatExpArg nativeGap029Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_028_Gen]

theorem nativeHeatStep_hExp_028_Gen : nativeHeatExpGen 28 = nativeHeat028Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_028_Gen, nativeHeat028Exp_formula]

theorem nativeHeatStep_hCoef_028_Gen : nativeHeatCoefGen 28 = nativeHeat028Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_028_Gen, nativeHeat028Coef_formula]

theorem nativeHeatStep_hInit_028_Gen : nativeHeatInitGen 28 = nativeHeat028Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_028_Gen, nativeHeatStep_hVar_028_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat028Init00_formula
    · exact nativeHeat028Init01_formula
    · exact nativeHeat028Init02_formula
    · exact nativeHeat028Init03_formula
    · exact nativeHeat028Init04_formula
    · exact nativeHeat028Init05_formula
    · exact nativeHeat028Init06_formula
    · exact nativeHeat028Init07_formula
    · exact nativeHeat028Init08_formula
    · exact nativeHeat028Init09_formula
    · exact nativeHeat028Init10_formula
    · exact nativeHeat028Init11_formula
    · exact nativeHeat028Init12_formula
    · exact nativeHeat028Init13_formula
    · exact nativeHeat028Init14_formula
    · exact nativeHeat028Init15_formula
    · exact nativeHeat028Init16_formula
    · exact nativeHeat028Init17_formula
    · exact nativeHeat028Init18_formula
    · exact nativeHeat028Init19_formula
    · exact nativeHeat028Init20_formula
theorem nativeHeatStep_hBase_028_Gen : nativeHeatBaseGen 28 = nativeHeat028Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_028_Gen, nativeHeatStep_hInit_028_Gen, nativeHeat028Base_formula]

theorem nativeHeatStep_hFixed_028_Gen : nativeHeatFixedGen 28 = nativeHeat028Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_028_Gen, nativeHeatStep_hFr_028_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat028Fixed01_formula
    · exact nativeHeat028Fixed02_formula
    · exact nativeHeat028Fixed03_formula
    · exact nativeHeat028Fixed04_formula
    · exact nativeHeat028Fixed05_formula
    · exact nativeHeat028Fixed06_formula
    · exact nativeHeat028Fixed07_formula
    · exact nativeHeat028Fixed08_formula
    · exact nativeHeat028Fixed09_formula
    · exact nativeHeat028Fixed10_formula
    · exact nativeHeat028Fixed11_formula
    · exact nativeHeat028Fixed12_formula
    · exact nativeHeat028Fixed13_formula
    · exact nativeHeat028Fixed14_formula
    · exact nativeHeat028Fixed15_formula
    · exact nativeHeat028Fixed16_formula
    · exact nativeHeat028Fixed17_formula
    · exact nativeHeat028Fixed18_formula
    · exact nativeHeat028Fixed19_formula
    · exact nativeHeat028Fixed20_formula

theorem nativeHeatStep_chk_028_Gen :
    nativeHeatPassRootsOk nativeGap029Old nativeHeat028Frames nativeHeat028Coef nativeHeat028Fixed nativeHeat028Base 48 nativeHeat028Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_028_Gen : NativeHeatStepPassNum 28 := by
  refine nativeHeatStepPassNum_of_literals 28 nativeGap029Old nativeHeat028Frames (nativeHeatExpArg nativeGap029Old)
    nativeHeat028Exp nativeHeat028Coef nativeHeat028Fixed nativeHeat028Init nativeHeat028Base nativeHeatStep_hOld_028_Gen
    nativeHeatStep_hFr_028_Gen nativeHeatStep_hArg_028_Gen nativeHeatStep_hExp_028_Gen
    nativeHeatStep_hCoef_028_Gen nativeHeatStep_hFixed_028_Gen
    nativeHeatStep_hInit_028_Gen nativeHeatStep_hBase_028_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_028_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_028_Gen :
    nativeHeatY0Gen 28 = nativeShiftedFrame 1 (min nativeGap029Old.x nativeGap029Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_028_Gen, nativeHeatStep_hInd_028_Gen]

theorem nativeHeatStepFrameNum_028_Gen : NativeHeatStepFrameNum 28 := by
  have h1 := nativeHeatStep_hOld_028_Gen
  have h2 := nativeHeatStep_hInd_028_Gen
  have h3 := nativeHeatStep_hVar_028_Gen
  have h4 := nativeHeatStep_hQm_028_Gen
  have h5 := nativeHeatStep_hQN_028_Gen
  have h6 := nativeHeatStep_hY0_028_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_028_Gen : NativeHeatStepIndivNum 28 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 28 (by norm_num)) = nativeGap029Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_028_Gen]; exact nativeGap029Old_source
  · rw [hc, nativeHeatStep_hInd_028_Gen]; exact nativeGap029Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_028_Gen : nativeHeatY48Gen 28 = nativeHeat028Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_028_Gen, nativeHeatStep_hFr_028_Gen,
    nativeHeatStep_hCoef_028_Gen, nativeHeatStep_hFixed_028_Gen,
    nativeHeatStep_hBase_028_Gen]
  exact nativeHeat028All48

theorem nativeHeatResultGen_028 : nativeHeatResultGen 28 = nativeHeat028Result := by
  rw [← nativeHeat028Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_028_Gen, nativeHeatStep_hY0_028_Gen, nativeHeatStep_hExp_028_Gen,
    nativeHeatStep_hInit_028_Gen, nativeHeatStep_hFixed_028_Gen]

end ASDExplicitGamma.Native

end
