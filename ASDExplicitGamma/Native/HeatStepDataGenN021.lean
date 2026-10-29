module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat021Complete
public import ASDExplicitGamma.Numerics.Native.Gap022Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_021_Gen : nativeHeatOldRowGen 21 = nativeGap022Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_021_Gen : nativeHeatIndividualGen 21 = nativeGap022Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_021_Gen : nativeHeatGenVariance 21 = nativeHeat021Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_021_Gen, nativeHeat021Variance_formula]

theorem nativeHeatStep_hSpec_021_Gen : nativeHeatGenSpectral 21 = nativeHeat021Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_021_Gen, nativeHeat021Variance_formula]

theorem nativeHeatStep_hQm_021_Gen : nativeHeatGenQm 21 = nativeHeat021Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_021_Gen, nativeHeatStep_hSpec_021_Gen,
    nativeHeat021Qm_formula]

theorem nativeHeatStep_hQN_021_Gen : nativeHeatQNGen 21 = nativeHeat021QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_021_Gen, nativeHeat021QN_formula]

theorem nativeHeatStep_hFr_021_Gen : nativeHeatFramesGen 21 = nativeHeat021Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_021_Gen, nativeHeatStep_hInd_021_Gen,
    nativeHeatStep_hVar_021_Gen, nativeHeatStep_hQN_021_Gen, nativeHeat021Frames_formula]

theorem nativeHeatStep_hArg_021_Gen : nativeHeatExpArgGen 21 = nativeHeatExpArg nativeGap022Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_021_Gen]

theorem nativeHeatStep_hExp_021_Gen : nativeHeatExpGen 21 = nativeHeat021Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_021_Gen, nativeHeat021Exp_formula]

theorem nativeHeatStep_hCoef_021_Gen : nativeHeatCoefGen 21 = nativeHeat021Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_021_Gen, nativeHeat021Coef_formula]

theorem nativeHeatStep_hInit_021_Gen : nativeHeatInitGen 21 = nativeHeat021Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_021_Gen, nativeHeatStep_hVar_021_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat021Init00_formula
    · exact nativeHeat021Init01_formula
    · exact nativeHeat021Init02_formula
    · exact nativeHeat021Init03_formula
    · exact nativeHeat021Init04_formula
    · exact nativeHeat021Init05_formula
    · exact nativeHeat021Init06_formula
    · exact nativeHeat021Init07_formula
    · exact nativeHeat021Init08_formula
    · exact nativeHeat021Init09_formula
    · exact nativeHeat021Init10_formula
    · exact nativeHeat021Init11_formula
    · exact nativeHeat021Init12_formula
    · exact nativeHeat021Init13_formula
    · exact nativeHeat021Init14_formula
    · exact nativeHeat021Init15_formula
    · exact nativeHeat021Init16_formula
    · exact nativeHeat021Init17_formula
    · exact nativeHeat021Init18_formula
    · exact nativeHeat021Init19_formula
    · exact nativeHeat021Init20_formula
theorem nativeHeatStep_hBase_021_Gen : nativeHeatBaseGen 21 = nativeHeat021Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_021_Gen, nativeHeatStep_hInit_021_Gen, nativeHeat021Base_formula]

theorem nativeHeatStep_hFixed_021_Gen : nativeHeatFixedGen 21 = nativeHeat021Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_021_Gen, nativeHeatStep_hFr_021_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat021Fixed01_formula
    · exact nativeHeat021Fixed02_formula
    · exact nativeHeat021Fixed03_formula
    · exact nativeHeat021Fixed04_formula
    · exact nativeHeat021Fixed05_formula
    · exact nativeHeat021Fixed06_formula
    · exact nativeHeat021Fixed07_formula
    · exact nativeHeat021Fixed08_formula
    · exact nativeHeat021Fixed09_formula
    · exact nativeHeat021Fixed10_formula
    · exact nativeHeat021Fixed11_formula
    · exact nativeHeat021Fixed12_formula
    · exact nativeHeat021Fixed13_formula
    · exact nativeHeat021Fixed14_formula
    · exact nativeHeat021Fixed15_formula
    · exact nativeHeat021Fixed16_formula
    · exact nativeHeat021Fixed17_formula
    · exact nativeHeat021Fixed18_formula
    · exact nativeHeat021Fixed19_formula
    · exact nativeHeat021Fixed20_formula

theorem nativeHeatStep_chk_021_Gen :
    nativeHeatPassRootsOk nativeGap022Old nativeHeat021Frames nativeHeat021Coef nativeHeat021Fixed nativeHeat021Base 48 nativeHeat021Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_021_Gen : NativeHeatStepPassNum 21 := by
  refine nativeHeatStepPassNum_of_literals 21 nativeGap022Old nativeHeat021Frames (nativeHeatExpArg nativeGap022Old)
    nativeHeat021Exp nativeHeat021Coef nativeHeat021Fixed nativeHeat021Init nativeHeat021Base nativeHeatStep_hOld_021_Gen
    nativeHeatStep_hFr_021_Gen nativeHeatStep_hArg_021_Gen nativeHeatStep_hExp_021_Gen
    nativeHeatStep_hCoef_021_Gen nativeHeatStep_hFixed_021_Gen
    nativeHeatStep_hInit_021_Gen nativeHeatStep_hBase_021_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_021_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_021_Gen :
    nativeHeatY0Gen 21 = nativeShiftedFrame 1 (min nativeGap022Old.x nativeGap022Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_021_Gen, nativeHeatStep_hInd_021_Gen]

theorem nativeHeatStepFrameNum_021_Gen : NativeHeatStepFrameNum 21 := by
  have h1 := nativeHeatStep_hOld_021_Gen
  have h2 := nativeHeatStep_hInd_021_Gen
  have h3 := nativeHeatStep_hVar_021_Gen
  have h4 := nativeHeatStep_hQm_021_Gen
  have h5 := nativeHeatStep_hQN_021_Gen
  have h6 := nativeHeatStep_hY0_021_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_021_Gen : NativeHeatStepIndivNum 21 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 21 (by norm_num)) = nativeGap022Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_021_Gen]; exact nativeGap022Old_source
  · rw [hc, nativeHeatStep_hInd_021_Gen]; exact nativeGap022Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_021_Gen : nativeHeatY48Gen 21 = nativeHeat021Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_021_Gen, nativeHeatStep_hFr_021_Gen,
    nativeHeatStep_hCoef_021_Gen, nativeHeatStep_hFixed_021_Gen,
    nativeHeatStep_hBase_021_Gen]
  exact nativeHeat021All48

theorem nativeHeatResultGen_021 : nativeHeatResultGen 21 = nativeHeat021Result := by
  rw [← nativeHeat021Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_021_Gen, nativeHeatStep_hY0_021_Gen, nativeHeatStep_hExp_021_Gen,
    nativeHeatStep_hInit_021_Gen, nativeHeatStep_hFixed_021_Gen]

end ASDExplicitGamma.Native

end
