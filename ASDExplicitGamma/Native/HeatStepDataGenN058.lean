module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat058Complete
public import ASDExplicitGamma.Numerics.Native.Gap059Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_058_Gen : nativeHeatOldRowGen 58 = nativeGap059Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_058_Gen : nativeHeatIndividualGen 58 = nativeGap059Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_058_Gen : nativeHeatGenVariance 58 = nativeHeat058Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_058_Gen, nativeHeat058Variance_formula]

theorem nativeHeatStep_hSpec_058_Gen : nativeHeatGenSpectral 58 = nativeHeat058Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_058_Gen, nativeHeat058Variance_formula]

theorem nativeHeatStep_hQm_058_Gen : nativeHeatGenQm 58 = nativeHeat058Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_058_Gen, nativeHeatStep_hSpec_058_Gen,
    nativeHeat058Qm_formula]

theorem nativeHeatStep_hQN_058_Gen : nativeHeatQNGen 58 = nativeHeat058QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_058_Gen, nativeHeat058QN_formula]

theorem nativeHeatStep_hFr_058_Gen : nativeHeatFramesGen 58 = nativeHeat058Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_058_Gen, nativeHeatStep_hInd_058_Gen,
    nativeHeatStep_hVar_058_Gen, nativeHeatStep_hQN_058_Gen, nativeHeat058Frames_formula]

theorem nativeHeatStep_hArg_058_Gen : nativeHeatExpArgGen 58 = nativeHeatExpArg nativeGap059Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_058_Gen]

theorem nativeHeatStep_hExp_058_Gen : nativeHeatExpGen 58 = nativeHeat058Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_058_Gen, nativeHeat058Exp_formula]

theorem nativeHeatStep_hCoef_058_Gen : nativeHeatCoefGen 58 = nativeHeat058Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_058_Gen, nativeHeat058Coef_formula]

theorem nativeHeatStep_hInit_058_Gen : nativeHeatInitGen 58 = nativeHeat058Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_058_Gen, nativeHeatStep_hVar_058_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat058Init00_formula
    · exact nativeHeat058Init01_formula
    · exact nativeHeat058Init02_formula
    · exact nativeHeat058Init03_formula
    · exact nativeHeat058Init04_formula
    · exact nativeHeat058Init05_formula
    · exact nativeHeat058Init06_formula
    · exact nativeHeat058Init07_formula
    · exact nativeHeat058Init08_formula
    · exact nativeHeat058Init09_formula
    · exact nativeHeat058Init10_formula
    · exact nativeHeat058Init11_formula
    · exact nativeHeat058Init12_formula
    · exact nativeHeat058Init13_formula
    · exact nativeHeat058Init14_formula
    · exact nativeHeat058Init15_formula
    · exact nativeHeat058Init16_formula
    · exact nativeHeat058Init17_formula
    · exact nativeHeat058Init18_formula
    · exact nativeHeat058Init19_formula
    · exact nativeHeat058Init20_formula
theorem nativeHeatStep_hBase_058_Gen : nativeHeatBaseGen 58 = nativeHeat058Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_058_Gen, nativeHeatStep_hInit_058_Gen, nativeHeat058Base_formula]

theorem nativeHeatStep_hFixed_058_Gen : nativeHeatFixedGen 58 = nativeHeat058Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_058_Gen, nativeHeatStep_hFr_058_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat058Fixed01_formula
    · exact nativeHeat058Fixed02_formula
    · exact nativeHeat058Fixed03_formula
    · exact nativeHeat058Fixed04_formula
    · exact nativeHeat058Fixed05_formula
    · exact nativeHeat058Fixed06_formula
    · exact nativeHeat058Fixed07_formula
    · exact nativeHeat058Fixed08_formula
    · exact nativeHeat058Fixed09_formula
    · exact nativeHeat058Fixed10_formula
    · exact nativeHeat058Fixed11_formula
    · exact nativeHeat058Fixed12_formula
    · exact nativeHeat058Fixed13_formula
    · exact nativeHeat058Fixed14_formula
    · exact nativeHeat058Fixed15_formula
    · exact nativeHeat058Fixed16_formula
    · exact nativeHeat058Fixed17_formula
    · exact nativeHeat058Fixed18_formula
    · exact nativeHeat058Fixed19_formula
    · exact nativeHeat058Fixed20_formula

theorem nativeHeatStep_chk_058_Gen :
    nativeHeatPassRootsOk nativeGap059Old nativeHeat058Frames nativeHeat058Coef nativeHeat058Fixed nativeHeat058Base 48 nativeHeat058Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_058_Gen : NativeHeatStepPassNum 58 := by
  refine nativeHeatStepPassNum_of_literals 58 nativeGap059Old nativeHeat058Frames (nativeHeatExpArg nativeGap059Old)
    nativeHeat058Exp nativeHeat058Coef nativeHeat058Fixed nativeHeat058Init nativeHeat058Base nativeHeatStep_hOld_058_Gen
    nativeHeatStep_hFr_058_Gen nativeHeatStep_hArg_058_Gen nativeHeatStep_hExp_058_Gen
    nativeHeatStep_hCoef_058_Gen nativeHeatStep_hFixed_058_Gen
    nativeHeatStep_hInit_058_Gen nativeHeatStep_hBase_058_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_058_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_058_Gen :
    nativeHeatY0Gen 58 = nativeShiftedFrame 1 (min nativeGap059Old.x nativeGap059Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_058_Gen, nativeHeatStep_hInd_058_Gen]

theorem nativeHeatStepFrameNum_058_Gen : NativeHeatStepFrameNum 58 := by
  have h1 := nativeHeatStep_hOld_058_Gen
  have h2 := nativeHeatStep_hInd_058_Gen
  have h3 := nativeHeatStep_hVar_058_Gen
  have h4 := nativeHeatStep_hQm_058_Gen
  have h5 := nativeHeatStep_hQN_058_Gen
  have h6 := nativeHeatStep_hY0_058_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_058_Gen : NativeHeatStepIndivNum 58 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 58 (by norm_num)) = nativeGap059Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_058_Gen]; exact nativeGap059Old_source
  · rw [hc, nativeHeatStep_hInd_058_Gen]; exact nativeGap059Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_058_Gen : nativeHeatY48Gen 58 = nativeHeat058Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_058_Gen, nativeHeatStep_hFr_058_Gen,
    nativeHeatStep_hCoef_058_Gen, nativeHeatStep_hFixed_058_Gen,
    nativeHeatStep_hBase_058_Gen]
  exact nativeHeat058All48

theorem nativeHeatResultGen_058 : nativeHeatResultGen 58 = nativeHeat058Result := by
  rw [← nativeHeat058Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_058_Gen, nativeHeatStep_hY0_058_Gen, nativeHeatStep_hExp_058_Gen,
    nativeHeatStep_hInit_058_Gen, nativeHeatStep_hFixed_058_Gen]

end ASDExplicitGamma.Native

end
