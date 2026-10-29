module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat081Complete
public import ASDExplicitGamma.Numerics.Native.Gap082Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_081_Gen : nativeHeatOldRowGen 81 = nativeGap082Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_081_Gen : nativeHeatIndividualGen 81 = nativeGap082Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_081_Gen : nativeHeatGenVariance 81 = nativeHeat081Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_081_Gen, nativeHeat081Variance_formula]

theorem nativeHeatStep_hSpec_081_Gen : nativeHeatGenSpectral 81 = nativeHeat081Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_081_Gen, nativeHeat081Variance_formula]

theorem nativeHeatStep_hQm_081_Gen : nativeHeatGenQm 81 = nativeHeat081Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_081_Gen, nativeHeatStep_hSpec_081_Gen,
    nativeHeat081Qm_formula]

theorem nativeHeatStep_hQN_081_Gen : nativeHeatQNGen 81 = nativeHeat081QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_081_Gen, nativeHeat081QN_formula]

theorem nativeHeatStep_hFr_081_Gen : nativeHeatFramesGen 81 = nativeHeat081Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_081_Gen, nativeHeatStep_hInd_081_Gen,
    nativeHeatStep_hVar_081_Gen, nativeHeatStep_hQN_081_Gen, nativeHeat081Frames_formula]

theorem nativeHeatStep_hArg_081_Gen : nativeHeatExpArgGen 81 = nativeHeatExpArg nativeGap082Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_081_Gen]

theorem nativeHeatStep_hExp_081_Gen : nativeHeatExpGen 81 = nativeHeat081Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_081_Gen, nativeHeat081Exp_formula]

theorem nativeHeatStep_hCoef_081_Gen : nativeHeatCoefGen 81 = nativeHeat081Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_081_Gen, nativeHeat081Coef_formula]

theorem nativeHeatStep_hInit_081_Gen : nativeHeatInitGen 81 = nativeHeat081Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_081_Gen, nativeHeatStep_hVar_081_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat081Init00_formula
    · exact nativeHeat081Init01_formula
    · exact nativeHeat081Init02_formula
    · exact nativeHeat081Init03_formula
    · exact nativeHeat081Init04_formula
    · exact nativeHeat081Init05_formula
    · exact nativeHeat081Init06_formula
    · exact nativeHeat081Init07_formula
    · exact nativeHeat081Init08_formula
    · exact nativeHeat081Init09_formula
    · exact nativeHeat081Init10_formula
    · exact nativeHeat081Init11_formula
    · exact nativeHeat081Init12_formula
    · exact nativeHeat081Init13_formula
    · exact nativeHeat081Init14_formula
    · exact nativeHeat081Init15_formula
    · exact nativeHeat081Init16_formula
    · exact nativeHeat081Init17_formula
    · exact nativeHeat081Init18_formula
    · exact nativeHeat081Init19_formula
    · exact nativeHeat081Init20_formula
theorem nativeHeatStep_hBase_081_Gen : nativeHeatBaseGen 81 = nativeHeat081Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_081_Gen, nativeHeatStep_hInit_081_Gen, nativeHeat081Base_formula]

theorem nativeHeatStep_hFixed_081_Gen : nativeHeatFixedGen 81 = nativeHeat081Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_081_Gen, nativeHeatStep_hFr_081_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat081Fixed01_formula
    · exact nativeHeat081Fixed02_formula
    · exact nativeHeat081Fixed03_formula
    · exact nativeHeat081Fixed04_formula
    · exact nativeHeat081Fixed05_formula
    · exact nativeHeat081Fixed06_formula
    · exact nativeHeat081Fixed07_formula
    · exact nativeHeat081Fixed08_formula
    · exact nativeHeat081Fixed09_formula
    · exact nativeHeat081Fixed10_formula
    · exact nativeHeat081Fixed11_formula
    · exact nativeHeat081Fixed12_formula
    · exact nativeHeat081Fixed13_formula
    · exact nativeHeat081Fixed14_formula
    · exact nativeHeat081Fixed15_formula
    · exact nativeHeat081Fixed16_formula
    · exact nativeHeat081Fixed17_formula
    · exact nativeHeat081Fixed18_formula
    · exact nativeHeat081Fixed19_formula
    · exact nativeHeat081Fixed20_formula

theorem nativeHeatStep_chk_081_Gen :
    nativeHeatPassRootsOk nativeGap082Old nativeHeat081Frames nativeHeat081Coef nativeHeat081Fixed nativeHeat081Base 48 nativeHeat081Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_081_Gen : NativeHeatStepPassNum 81 := by
  refine nativeHeatStepPassNum_of_literals 81 nativeGap082Old nativeHeat081Frames (nativeHeatExpArg nativeGap082Old)
    nativeHeat081Exp nativeHeat081Coef nativeHeat081Fixed nativeHeat081Init nativeHeat081Base nativeHeatStep_hOld_081_Gen
    nativeHeatStep_hFr_081_Gen nativeHeatStep_hArg_081_Gen nativeHeatStep_hExp_081_Gen
    nativeHeatStep_hCoef_081_Gen nativeHeatStep_hFixed_081_Gen
    nativeHeatStep_hInit_081_Gen nativeHeatStep_hBase_081_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_081_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_081_Gen :
    nativeHeatY0Gen 81 = nativeShiftedFrame 1 (min nativeGap082Old.x nativeGap082Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_081_Gen, nativeHeatStep_hInd_081_Gen]

theorem nativeHeatStepFrameNum_081_Gen : NativeHeatStepFrameNum 81 := by
  have h1 := nativeHeatStep_hOld_081_Gen
  have h2 := nativeHeatStep_hInd_081_Gen
  have h3 := nativeHeatStep_hVar_081_Gen
  have h4 := nativeHeatStep_hQm_081_Gen
  have h5 := nativeHeatStep_hQN_081_Gen
  have h6 := nativeHeatStep_hY0_081_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_081_Gen : NativeHeatStepIndivNum 81 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 81 (by norm_num)) = nativeGap082Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_081_Gen]; exact nativeGap082Old_source
  · rw [hc, nativeHeatStep_hInd_081_Gen]; exact nativeGap082Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_081_Gen : nativeHeatY48Gen 81 = nativeHeat081Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_081_Gen, nativeHeatStep_hFr_081_Gen,
    nativeHeatStep_hCoef_081_Gen, nativeHeatStep_hFixed_081_Gen,
    nativeHeatStep_hBase_081_Gen]
  exact nativeHeat081All48

theorem nativeHeatResultGen_081 : nativeHeatResultGen 81 = nativeHeat081Result := by
  rw [← nativeHeat081Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_081_Gen, nativeHeatStep_hY0_081_Gen, nativeHeatStep_hExp_081_Gen,
    nativeHeatStep_hInit_081_Gen, nativeHeatStep_hFixed_081_Gen]

end ASDExplicitGamma.Native

end
