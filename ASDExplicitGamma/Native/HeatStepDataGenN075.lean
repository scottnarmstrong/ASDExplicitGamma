module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat075Complete
public import ASDExplicitGamma.Numerics.Native.Gap076Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_075_Gen : nativeHeatOldRowGen 75 = nativeGap076Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_075_Gen : nativeHeatIndividualGen 75 = nativeGap076Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_075_Gen : nativeHeatGenVariance 75 = nativeHeat075Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_075_Gen, nativeHeat075Variance_formula]

theorem nativeHeatStep_hSpec_075_Gen : nativeHeatGenSpectral 75 = nativeHeat075Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_075_Gen, nativeHeat075Variance_formula]

theorem nativeHeatStep_hQm_075_Gen : nativeHeatGenQm 75 = nativeHeat075Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_075_Gen, nativeHeatStep_hSpec_075_Gen,
    nativeHeat075Qm_formula]

theorem nativeHeatStep_hQN_075_Gen : nativeHeatQNGen 75 = nativeHeat075QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_075_Gen, nativeHeat075QN_formula]

theorem nativeHeatStep_hFr_075_Gen : nativeHeatFramesGen 75 = nativeHeat075Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_075_Gen, nativeHeatStep_hInd_075_Gen,
    nativeHeatStep_hVar_075_Gen, nativeHeatStep_hQN_075_Gen, nativeHeat075Frames_formula]

theorem nativeHeatStep_hArg_075_Gen : nativeHeatExpArgGen 75 = nativeHeatExpArg nativeGap076Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_075_Gen]

theorem nativeHeatStep_hExp_075_Gen : nativeHeatExpGen 75 = nativeHeat075Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_075_Gen, nativeHeat075Exp_formula]

theorem nativeHeatStep_hCoef_075_Gen : nativeHeatCoefGen 75 = nativeHeat075Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_075_Gen, nativeHeat075Coef_formula]

theorem nativeHeatStep_hInit_075_Gen : nativeHeatInitGen 75 = nativeHeat075Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_075_Gen, nativeHeatStep_hVar_075_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat075Init00_formula
    · exact nativeHeat075Init01_formula
    · exact nativeHeat075Init02_formula
    · exact nativeHeat075Init03_formula
    · exact nativeHeat075Init04_formula
    · exact nativeHeat075Init05_formula
    · exact nativeHeat075Init06_formula
    · exact nativeHeat075Init07_formula
    · exact nativeHeat075Init08_formula
    · exact nativeHeat075Init09_formula
    · exact nativeHeat075Init10_formula
    · exact nativeHeat075Init11_formula
    · exact nativeHeat075Init12_formula
    · exact nativeHeat075Init13_formula
    · exact nativeHeat075Init14_formula
    · exact nativeHeat075Init15_formula
    · exact nativeHeat075Init16_formula
    · exact nativeHeat075Init17_formula
    · exact nativeHeat075Init18_formula
    · exact nativeHeat075Init19_formula
    · exact nativeHeat075Init20_formula
theorem nativeHeatStep_hBase_075_Gen : nativeHeatBaseGen 75 = nativeHeat075Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_075_Gen, nativeHeatStep_hInit_075_Gen, nativeHeat075Base_formula]

theorem nativeHeatStep_hFixed_075_Gen : nativeHeatFixedGen 75 = nativeHeat075Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_075_Gen, nativeHeatStep_hFr_075_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat075Fixed01_formula
    · exact nativeHeat075Fixed02_formula
    · exact nativeHeat075Fixed03_formula
    · exact nativeHeat075Fixed04_formula
    · exact nativeHeat075Fixed05_formula
    · exact nativeHeat075Fixed06_formula
    · exact nativeHeat075Fixed07_formula
    · exact nativeHeat075Fixed08_formula
    · exact nativeHeat075Fixed09_formula
    · exact nativeHeat075Fixed10_formula
    · exact nativeHeat075Fixed11_formula
    · exact nativeHeat075Fixed12_formula
    · exact nativeHeat075Fixed13_formula
    · exact nativeHeat075Fixed14_formula
    · exact nativeHeat075Fixed15_formula
    · exact nativeHeat075Fixed16_formula
    · exact nativeHeat075Fixed17_formula
    · exact nativeHeat075Fixed18_formula
    · exact nativeHeat075Fixed19_formula
    · exact nativeHeat075Fixed20_formula

theorem nativeHeatStep_chk_075_Gen :
    nativeHeatPassRootsOk nativeGap076Old nativeHeat075Frames nativeHeat075Coef nativeHeat075Fixed nativeHeat075Base 48 nativeHeat075Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_075_Gen : NativeHeatStepPassNum 75 := by
  refine nativeHeatStepPassNum_of_literals 75 nativeGap076Old nativeHeat075Frames (nativeHeatExpArg nativeGap076Old)
    nativeHeat075Exp nativeHeat075Coef nativeHeat075Fixed nativeHeat075Init nativeHeat075Base nativeHeatStep_hOld_075_Gen
    nativeHeatStep_hFr_075_Gen nativeHeatStep_hArg_075_Gen nativeHeatStep_hExp_075_Gen
    nativeHeatStep_hCoef_075_Gen nativeHeatStep_hFixed_075_Gen
    nativeHeatStep_hInit_075_Gen nativeHeatStep_hBase_075_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_075_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_075_Gen :
    nativeHeatY0Gen 75 = nativeShiftedFrame 1 (min nativeGap076Old.x nativeGap076Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_075_Gen, nativeHeatStep_hInd_075_Gen]

theorem nativeHeatStepFrameNum_075_Gen : NativeHeatStepFrameNum 75 := by
  have h1 := nativeHeatStep_hOld_075_Gen
  have h2 := nativeHeatStep_hInd_075_Gen
  have h3 := nativeHeatStep_hVar_075_Gen
  have h4 := nativeHeatStep_hQm_075_Gen
  have h5 := nativeHeatStep_hQN_075_Gen
  have h6 := nativeHeatStep_hY0_075_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_075_Gen : NativeHeatStepIndivNum 75 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 75 (by norm_num)) = nativeGap076Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_075_Gen]; exact nativeGap076Old_source
  · rw [hc, nativeHeatStep_hInd_075_Gen]; exact nativeGap076Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_075_Gen : nativeHeatY48Gen 75 = nativeHeat075Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_075_Gen, nativeHeatStep_hFr_075_Gen,
    nativeHeatStep_hCoef_075_Gen, nativeHeatStep_hFixed_075_Gen,
    nativeHeatStep_hBase_075_Gen]
  exact nativeHeat075All48

theorem nativeHeatResultGen_075 : nativeHeatResultGen 75 = nativeHeat075Result := by
  rw [← nativeHeat075Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_075_Gen, nativeHeatStep_hY0_075_Gen, nativeHeatStep_hExp_075_Gen,
    nativeHeatStep_hInit_075_Gen, nativeHeatStep_hFixed_075_Gen]

end ASDExplicitGamma.Native

end
