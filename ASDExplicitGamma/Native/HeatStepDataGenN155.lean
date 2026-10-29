module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat155Complete
public import ASDExplicitGamma.Numerics.Native.Gap156Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_155_Gen : nativeHeatOldRowGen 155 = nativeGap156Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_155_Gen : nativeHeatIndividualGen 155 = nativeGap156Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_155_Gen : nativeHeatGenVariance 155 = nativeHeat155Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_155_Gen, nativeHeat155Variance_formula]

theorem nativeHeatStep_hSpec_155_Gen : nativeHeatGenSpectral 155 = nativeHeat155Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_155_Gen, nativeHeat155Variance_formula]

theorem nativeHeatStep_hQm_155_Gen : nativeHeatGenQm 155 = nativeHeat155Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_155_Gen, nativeHeatStep_hSpec_155_Gen,
    nativeHeat155Qm_formula]

theorem nativeHeatStep_hQN_155_Gen : nativeHeatQNGen 155 = nativeHeat155QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_155_Gen, nativeHeat155QN_formula]

theorem nativeHeatStep_hFr_155_Gen : nativeHeatFramesGen 155 = nativeHeat155Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_155_Gen, nativeHeatStep_hInd_155_Gen,
    nativeHeatStep_hVar_155_Gen, nativeHeatStep_hQN_155_Gen, nativeHeat155Frames_formula]

theorem nativeHeatStep_hArg_155_Gen : nativeHeatExpArgGen 155 = nativeHeatExpArg nativeGap156Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_155_Gen]

theorem nativeHeatStep_hExp_155_Gen : nativeHeatExpGen 155 = nativeHeat155Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_155_Gen, nativeHeat155Exp_formula]

theorem nativeHeatStep_hCoef_155_Gen : nativeHeatCoefGen 155 = nativeHeat155Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_155_Gen, nativeHeat155Coef_formula]

theorem nativeHeatStep_hInit_155_Gen : nativeHeatInitGen 155 = nativeHeat155Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_155_Gen, nativeHeatStep_hVar_155_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat155Init00_formula
    · exact nativeHeat155Init01_formula
    · exact nativeHeat155Init02_formula
    · exact nativeHeat155Init03_formula
    · exact nativeHeat155Init04_formula
    · exact nativeHeat155Init05_formula
    · exact nativeHeat155Init06_formula
    · exact nativeHeat155Init07_formula
    · exact nativeHeat155Init08_formula
    · exact nativeHeat155Init09_formula
    · exact nativeHeat155Init10_formula
    · exact nativeHeat155Init11_formula
    · exact nativeHeat155Init12_formula
    · exact nativeHeat155Init13_formula
    · exact nativeHeat155Init14_formula
    · exact nativeHeat155Init15_formula
    · exact nativeHeat155Init16_formula
    · exact nativeHeat155Init17_formula
    · exact nativeHeat155Init18_formula
    · exact nativeHeat155Init19_formula
    · exact nativeHeat155Init20_formula
theorem nativeHeatStep_hBase_155_Gen : nativeHeatBaseGen 155 = nativeHeat155Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_155_Gen, nativeHeatStep_hInit_155_Gen, nativeHeat155Base_formula]

theorem nativeHeatStep_hFixed_155_Gen : nativeHeatFixedGen 155 = nativeHeat155Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_155_Gen, nativeHeatStep_hFr_155_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat155Fixed01_formula
    · exact nativeHeat155Fixed02_formula
    · exact nativeHeat155Fixed03_formula
    · exact nativeHeat155Fixed04_formula
    · exact nativeHeat155Fixed05_formula
    · exact nativeHeat155Fixed06_formula
    · exact nativeHeat155Fixed07_formula
    · exact nativeHeat155Fixed08_formula
    · exact nativeHeat155Fixed09_formula
    · exact nativeHeat155Fixed10_formula
    · exact nativeHeat155Fixed11_formula
    · exact nativeHeat155Fixed12_formula
    · exact nativeHeat155Fixed13_formula
    · exact nativeHeat155Fixed14_formula
    · exact nativeHeat155Fixed15_formula
    · exact nativeHeat155Fixed16_formula
    · exact nativeHeat155Fixed17_formula
    · exact nativeHeat155Fixed18_formula
    · exact nativeHeat155Fixed19_formula
    · exact nativeHeat155Fixed20_formula

theorem nativeHeatStep_chk_155_Gen :
    nativeHeatPassRootsOk nativeGap156Old nativeHeat155Frames nativeHeat155Coef nativeHeat155Fixed nativeHeat155Base 48 nativeHeat155Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_155_Gen : NativeHeatStepPassNum 155 := by
  refine nativeHeatStepPassNum_of_literals 155 nativeGap156Old nativeHeat155Frames (nativeHeatExpArg nativeGap156Old)
    nativeHeat155Exp nativeHeat155Coef nativeHeat155Fixed nativeHeat155Init nativeHeat155Base nativeHeatStep_hOld_155_Gen
    nativeHeatStep_hFr_155_Gen nativeHeatStep_hArg_155_Gen nativeHeatStep_hExp_155_Gen
    nativeHeatStep_hCoef_155_Gen nativeHeatStep_hFixed_155_Gen
    nativeHeatStep_hInit_155_Gen nativeHeatStep_hBase_155_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_155_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_155_Gen :
    nativeHeatY0Gen 155 = nativeShiftedFrame 1 (min nativeGap156Old.x nativeGap156Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_155_Gen, nativeHeatStep_hInd_155_Gen]

theorem nativeHeatStepFrameNum_155_Gen : NativeHeatStepFrameNum 155 := by
  have h1 := nativeHeatStep_hOld_155_Gen
  have h2 := nativeHeatStep_hInd_155_Gen
  have h3 := nativeHeatStep_hVar_155_Gen
  have h4 := nativeHeatStep_hQm_155_Gen
  have h5 := nativeHeatStep_hQN_155_Gen
  have h6 := nativeHeatStep_hY0_155_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_155_Gen : NativeHeatStepIndivNum 155 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 155 (by norm_num)) = nativeGap156Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_155_Gen]; exact nativeGap156Old_source
  · rw [hc, nativeHeatStep_hInd_155_Gen]; exact nativeGap156Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_155_Gen : nativeHeatY48Gen 155 = nativeHeat155Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_155_Gen, nativeHeatStep_hFr_155_Gen,
    nativeHeatStep_hCoef_155_Gen, nativeHeatStep_hFixed_155_Gen,
    nativeHeatStep_hBase_155_Gen]
  exact nativeHeat155All48

theorem nativeHeatResultGen_155 : nativeHeatResultGen 155 = nativeHeat155Result := by
  rw [← nativeHeat155Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_155_Gen, nativeHeatStep_hY0_155_Gen, nativeHeatStep_hExp_155_Gen,
    nativeHeatStep_hInit_155_Gen, nativeHeatStep_hFixed_155_Gen]

end ASDExplicitGamma.Native

end
