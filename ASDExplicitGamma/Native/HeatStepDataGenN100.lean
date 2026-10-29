module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat100Complete
public import ASDExplicitGamma.Numerics.Native.Gap101Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_100_Gen : nativeHeatOldRowGen 100 = nativeGap101Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_100_Gen : nativeHeatIndividualGen 100 = nativeGap101Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_100_Gen : nativeHeatGenVariance 100 = nativeHeat100Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_100_Gen, nativeHeat100Variance_formula]

theorem nativeHeatStep_hSpec_100_Gen : nativeHeatGenSpectral 100 = nativeHeat100Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_100_Gen, nativeHeat100Variance_formula]

theorem nativeHeatStep_hQm_100_Gen : nativeHeatGenQm 100 = nativeHeat100Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_100_Gen, nativeHeatStep_hSpec_100_Gen,
    nativeHeat100Qm_formula]

theorem nativeHeatStep_hQN_100_Gen : nativeHeatQNGen 100 = nativeHeat100QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_100_Gen, nativeHeat100QN_formula]

theorem nativeHeatStep_hFr_100_Gen : nativeHeatFramesGen 100 = nativeHeat100Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_100_Gen, nativeHeatStep_hInd_100_Gen,
    nativeHeatStep_hVar_100_Gen, nativeHeatStep_hQN_100_Gen, nativeHeat100Frames_formula]

theorem nativeHeatStep_hArg_100_Gen : nativeHeatExpArgGen 100 = nativeHeatExpArg nativeGap101Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_100_Gen]

theorem nativeHeatStep_hExp_100_Gen : nativeHeatExpGen 100 = nativeHeat100Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_100_Gen, nativeHeat100Exp_formula]

theorem nativeHeatStep_hCoef_100_Gen : nativeHeatCoefGen 100 = nativeHeat100Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_100_Gen, nativeHeat100Coef_formula]

theorem nativeHeatStep_hInit_100_Gen : nativeHeatInitGen 100 = nativeHeat100Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_100_Gen, nativeHeatStep_hVar_100_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat100Init00_formula
    · exact nativeHeat100Init01_formula
    · exact nativeHeat100Init02_formula
    · exact nativeHeat100Init03_formula
    · exact nativeHeat100Init04_formula
    · exact nativeHeat100Init05_formula
    · exact nativeHeat100Init06_formula
    · exact nativeHeat100Init07_formula
    · exact nativeHeat100Init08_formula
    · exact nativeHeat100Init09_formula
    · exact nativeHeat100Init10_formula
    · exact nativeHeat100Init11_formula
    · exact nativeHeat100Init12_formula
    · exact nativeHeat100Init13_formula
    · exact nativeHeat100Init14_formula
    · exact nativeHeat100Init15_formula
    · exact nativeHeat100Init16_formula
    · exact nativeHeat100Init17_formula
    · exact nativeHeat100Init18_formula
    · exact nativeHeat100Init19_formula
    · exact nativeHeat100Init20_formula
theorem nativeHeatStep_hBase_100_Gen : nativeHeatBaseGen 100 = nativeHeat100Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_100_Gen, nativeHeatStep_hInit_100_Gen, nativeHeat100Base_formula]

theorem nativeHeatStep_hFixed_100_Gen : nativeHeatFixedGen 100 = nativeHeat100Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_100_Gen, nativeHeatStep_hFr_100_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat100Fixed01_formula
    · exact nativeHeat100Fixed02_formula
    · exact nativeHeat100Fixed03_formula
    · exact nativeHeat100Fixed04_formula
    · exact nativeHeat100Fixed05_formula
    · exact nativeHeat100Fixed06_formula
    · exact nativeHeat100Fixed07_formula
    · exact nativeHeat100Fixed08_formula
    · exact nativeHeat100Fixed09_formula
    · exact nativeHeat100Fixed10_formula
    · exact nativeHeat100Fixed11_formula
    · exact nativeHeat100Fixed12_formula
    · exact nativeHeat100Fixed13_formula
    · exact nativeHeat100Fixed14_formula
    · exact nativeHeat100Fixed15_formula
    · exact nativeHeat100Fixed16_formula
    · exact nativeHeat100Fixed17_formula
    · exact nativeHeat100Fixed18_formula
    · exact nativeHeat100Fixed19_formula
    · exact nativeHeat100Fixed20_formula

theorem nativeHeatStep_chk_100_Gen :
    nativeHeatPassRootsOk nativeGap101Old nativeHeat100Frames nativeHeat100Coef nativeHeat100Fixed nativeHeat100Base 48 nativeHeat100Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_100_Gen : NativeHeatStepPassNum 100 := by
  refine nativeHeatStepPassNum_of_literals 100 nativeGap101Old nativeHeat100Frames (nativeHeatExpArg nativeGap101Old)
    nativeHeat100Exp nativeHeat100Coef nativeHeat100Fixed nativeHeat100Init nativeHeat100Base nativeHeatStep_hOld_100_Gen
    nativeHeatStep_hFr_100_Gen nativeHeatStep_hArg_100_Gen nativeHeatStep_hExp_100_Gen
    nativeHeatStep_hCoef_100_Gen nativeHeatStep_hFixed_100_Gen
    nativeHeatStep_hInit_100_Gen nativeHeatStep_hBase_100_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_100_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_100_Gen :
    nativeHeatY0Gen 100 = nativeShiftedFrame 1 (min nativeGap101Old.x nativeGap101Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_100_Gen, nativeHeatStep_hInd_100_Gen]

theorem nativeHeatStepFrameNum_100_Gen : NativeHeatStepFrameNum 100 := by
  have h1 := nativeHeatStep_hOld_100_Gen
  have h2 := nativeHeatStep_hInd_100_Gen
  have h3 := nativeHeatStep_hVar_100_Gen
  have h4 := nativeHeatStep_hQm_100_Gen
  have h5 := nativeHeatStep_hQN_100_Gen
  have h6 := nativeHeatStep_hY0_100_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_100_Gen : NativeHeatStepIndivNum 100 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 100 (by norm_num)) = nativeGap101Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_100_Gen]; exact nativeGap101Old_source
  · rw [hc, nativeHeatStep_hInd_100_Gen]; exact nativeGap101Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_100_Gen : nativeHeatY48Gen 100 = nativeHeat100Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_100_Gen, nativeHeatStep_hFr_100_Gen,
    nativeHeatStep_hCoef_100_Gen, nativeHeatStep_hFixed_100_Gen,
    nativeHeatStep_hBase_100_Gen]
  exact nativeHeat100All48

theorem nativeHeatResultGen_100 : nativeHeatResultGen 100 = nativeHeat100Result := by
  rw [← nativeHeat100Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_100_Gen, nativeHeatStep_hY0_100_Gen, nativeHeatStep_hExp_100_Gen,
    nativeHeatStep_hInit_100_Gen, nativeHeatStep_hFixed_100_Gen]

end ASDExplicitGamma.Native

end
