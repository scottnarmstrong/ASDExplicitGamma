module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat061Complete
public import ASDExplicitGamma.Numerics.Native.Gap062Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_061_Gen : nativeHeatOldRowGen 61 = nativeGap062Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_061_Gen : nativeHeatIndividualGen 61 = nativeGap062Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_061_Gen : nativeHeatGenVariance 61 = nativeHeat061Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_061_Gen, nativeHeat061Variance_formula]

theorem nativeHeatStep_hSpec_061_Gen : nativeHeatGenSpectral 61 = nativeHeat061Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_061_Gen, nativeHeat061Variance_formula]

theorem nativeHeatStep_hQm_061_Gen : nativeHeatGenQm 61 = nativeHeat061Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_061_Gen, nativeHeatStep_hSpec_061_Gen,
    nativeHeat061Qm_formula]

theorem nativeHeatStep_hQN_061_Gen : nativeHeatQNGen 61 = nativeHeat061QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_061_Gen, nativeHeat061QN_formula]

theorem nativeHeatStep_hFr_061_Gen : nativeHeatFramesGen 61 = nativeHeat061Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_061_Gen, nativeHeatStep_hInd_061_Gen,
    nativeHeatStep_hVar_061_Gen, nativeHeatStep_hQN_061_Gen, nativeHeat061Frames_formula]

theorem nativeHeatStep_hArg_061_Gen : nativeHeatExpArgGen 61 = nativeHeatExpArg nativeGap062Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_061_Gen]

theorem nativeHeatStep_hExp_061_Gen : nativeHeatExpGen 61 = nativeHeat061Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_061_Gen, nativeHeat061Exp_formula]

theorem nativeHeatStep_hCoef_061_Gen : nativeHeatCoefGen 61 = nativeHeat061Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_061_Gen, nativeHeat061Coef_formula]

theorem nativeHeatStep_hInit_061_Gen : nativeHeatInitGen 61 = nativeHeat061Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_061_Gen, nativeHeatStep_hVar_061_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat061Init00_formula
    · exact nativeHeat061Init01_formula
    · exact nativeHeat061Init02_formula
    · exact nativeHeat061Init03_formula
    · exact nativeHeat061Init04_formula
    · exact nativeHeat061Init05_formula
    · exact nativeHeat061Init06_formula
    · exact nativeHeat061Init07_formula
    · exact nativeHeat061Init08_formula
    · exact nativeHeat061Init09_formula
    · exact nativeHeat061Init10_formula
    · exact nativeHeat061Init11_formula
    · exact nativeHeat061Init12_formula
    · exact nativeHeat061Init13_formula
    · exact nativeHeat061Init14_formula
    · exact nativeHeat061Init15_formula
    · exact nativeHeat061Init16_formula
    · exact nativeHeat061Init17_formula
    · exact nativeHeat061Init18_formula
    · exact nativeHeat061Init19_formula
    · exact nativeHeat061Init20_formula
theorem nativeHeatStep_hBase_061_Gen : nativeHeatBaseGen 61 = nativeHeat061Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_061_Gen, nativeHeatStep_hInit_061_Gen, nativeHeat061Base_formula]

theorem nativeHeatStep_hFixed_061_Gen : nativeHeatFixedGen 61 = nativeHeat061Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_061_Gen, nativeHeatStep_hFr_061_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat061Fixed01_formula
    · exact nativeHeat061Fixed02_formula
    · exact nativeHeat061Fixed03_formula
    · exact nativeHeat061Fixed04_formula
    · exact nativeHeat061Fixed05_formula
    · exact nativeHeat061Fixed06_formula
    · exact nativeHeat061Fixed07_formula
    · exact nativeHeat061Fixed08_formula
    · exact nativeHeat061Fixed09_formula
    · exact nativeHeat061Fixed10_formula
    · exact nativeHeat061Fixed11_formula
    · exact nativeHeat061Fixed12_formula
    · exact nativeHeat061Fixed13_formula
    · exact nativeHeat061Fixed14_formula
    · exact nativeHeat061Fixed15_formula
    · exact nativeHeat061Fixed16_formula
    · exact nativeHeat061Fixed17_formula
    · exact nativeHeat061Fixed18_formula
    · exact nativeHeat061Fixed19_formula
    · exact nativeHeat061Fixed20_formula

theorem nativeHeatStep_chk_061_Gen :
    nativeHeatPassRootsOk nativeGap062Old nativeHeat061Frames nativeHeat061Coef nativeHeat061Fixed nativeHeat061Base 48 nativeHeat061Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_061_Gen : NativeHeatStepPassNum 61 := by
  refine nativeHeatStepPassNum_of_literals 61 nativeGap062Old nativeHeat061Frames (nativeHeatExpArg nativeGap062Old)
    nativeHeat061Exp nativeHeat061Coef nativeHeat061Fixed nativeHeat061Init nativeHeat061Base nativeHeatStep_hOld_061_Gen
    nativeHeatStep_hFr_061_Gen nativeHeatStep_hArg_061_Gen nativeHeatStep_hExp_061_Gen
    nativeHeatStep_hCoef_061_Gen nativeHeatStep_hFixed_061_Gen
    nativeHeatStep_hInit_061_Gen nativeHeatStep_hBase_061_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_061_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_061_Gen :
    nativeHeatY0Gen 61 = nativeShiftedFrame 1 (min nativeGap062Old.x nativeGap062Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_061_Gen, nativeHeatStep_hInd_061_Gen]

theorem nativeHeatStepFrameNum_061_Gen : NativeHeatStepFrameNum 61 := by
  have h1 := nativeHeatStep_hOld_061_Gen
  have h2 := nativeHeatStep_hInd_061_Gen
  have h3 := nativeHeatStep_hVar_061_Gen
  have h4 := nativeHeatStep_hQm_061_Gen
  have h5 := nativeHeatStep_hQN_061_Gen
  have h6 := nativeHeatStep_hY0_061_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_061_Gen : NativeHeatStepIndivNum 61 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 61 (by norm_num)) = nativeGap062Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_061_Gen]; exact nativeGap062Old_source
  · rw [hc, nativeHeatStep_hInd_061_Gen]; exact nativeGap062Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_061_Gen : nativeHeatY48Gen 61 = nativeHeat061Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_061_Gen, nativeHeatStep_hFr_061_Gen,
    nativeHeatStep_hCoef_061_Gen, nativeHeatStep_hFixed_061_Gen,
    nativeHeatStep_hBase_061_Gen]
  exact nativeHeat061All48

theorem nativeHeatResultGen_061 : nativeHeatResultGen 61 = nativeHeat061Result := by
  rw [← nativeHeat061Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_061_Gen, nativeHeatStep_hY0_061_Gen, nativeHeatStep_hExp_061_Gen,
    nativeHeatStep_hInit_061_Gen, nativeHeatStep_hFixed_061_Gen]

end ASDExplicitGamma.Native

end
