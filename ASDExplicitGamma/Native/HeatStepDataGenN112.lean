module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat112Complete
public import ASDExplicitGamma.Numerics.Native.Gap113Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_112_Gen : nativeHeatOldRowGen 112 = nativeGap113Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_112_Gen : nativeHeatIndividualGen 112 = nativeGap113Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_112_Gen : nativeHeatGenVariance 112 = nativeHeat112Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_112_Gen, nativeHeat112Variance_formula]

theorem nativeHeatStep_hSpec_112_Gen : nativeHeatGenSpectral 112 = nativeHeat112Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_112_Gen, nativeHeat112Variance_formula]

theorem nativeHeatStep_hQm_112_Gen : nativeHeatGenQm 112 = nativeHeat112Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_112_Gen, nativeHeatStep_hSpec_112_Gen,
    nativeHeat112Qm_formula]

theorem nativeHeatStep_hQN_112_Gen : nativeHeatQNGen 112 = nativeHeat112QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_112_Gen, nativeHeat112QN_formula]

theorem nativeHeatStep_hFr_112_Gen : nativeHeatFramesGen 112 = nativeHeat112Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_112_Gen, nativeHeatStep_hInd_112_Gen,
    nativeHeatStep_hVar_112_Gen, nativeHeatStep_hQN_112_Gen, nativeHeat112Frames_formula]

theorem nativeHeatStep_hArg_112_Gen : nativeHeatExpArgGen 112 = nativeHeatExpArg nativeGap113Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_112_Gen]

theorem nativeHeatStep_hExp_112_Gen : nativeHeatExpGen 112 = nativeHeat112Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_112_Gen, nativeHeat112Exp_formula]

theorem nativeHeatStep_hCoef_112_Gen : nativeHeatCoefGen 112 = nativeHeat112Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_112_Gen, nativeHeat112Coef_formula]

theorem nativeHeatStep_hInit_112_Gen : nativeHeatInitGen 112 = nativeHeat112Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_112_Gen, nativeHeatStep_hVar_112_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat112Init00_formula
    · exact nativeHeat112Init01_formula
    · exact nativeHeat112Init02_formula
    · exact nativeHeat112Init03_formula
    · exact nativeHeat112Init04_formula
    · exact nativeHeat112Init05_formula
    · exact nativeHeat112Init06_formula
    · exact nativeHeat112Init07_formula
    · exact nativeHeat112Init08_formula
    · exact nativeHeat112Init09_formula
    · exact nativeHeat112Init10_formula
    · exact nativeHeat112Init11_formula
    · exact nativeHeat112Init12_formula
    · exact nativeHeat112Init13_formula
    · exact nativeHeat112Init14_formula
    · exact nativeHeat112Init15_formula
    · exact nativeHeat112Init16_formula
    · exact nativeHeat112Init17_formula
    · exact nativeHeat112Init18_formula
    · exact nativeHeat112Init19_formula
    · exact nativeHeat112Init20_formula
theorem nativeHeatStep_hBase_112_Gen : nativeHeatBaseGen 112 = nativeHeat112Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_112_Gen, nativeHeatStep_hInit_112_Gen, nativeHeat112Base_formula]

theorem nativeHeatStep_hFixed_112_Gen : nativeHeatFixedGen 112 = nativeHeat112Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_112_Gen, nativeHeatStep_hFr_112_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat112Fixed01_formula
    · exact nativeHeat112Fixed02_formula
    · exact nativeHeat112Fixed03_formula
    · exact nativeHeat112Fixed04_formula
    · exact nativeHeat112Fixed05_formula
    · exact nativeHeat112Fixed06_formula
    · exact nativeHeat112Fixed07_formula
    · exact nativeHeat112Fixed08_formula
    · exact nativeHeat112Fixed09_formula
    · exact nativeHeat112Fixed10_formula
    · exact nativeHeat112Fixed11_formula
    · exact nativeHeat112Fixed12_formula
    · exact nativeHeat112Fixed13_formula
    · exact nativeHeat112Fixed14_formula
    · exact nativeHeat112Fixed15_formula
    · exact nativeHeat112Fixed16_formula
    · exact nativeHeat112Fixed17_formula
    · exact nativeHeat112Fixed18_formula
    · exact nativeHeat112Fixed19_formula
    · exact nativeHeat112Fixed20_formula

theorem nativeHeatStep_chk_112_Gen :
    nativeHeatPassRootsOk nativeGap113Old nativeHeat112Frames nativeHeat112Coef nativeHeat112Fixed nativeHeat112Base 48 nativeHeat112Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_112_Gen : NativeHeatStepPassNum 112 := by
  refine nativeHeatStepPassNum_of_literals 112 nativeGap113Old nativeHeat112Frames (nativeHeatExpArg nativeGap113Old)
    nativeHeat112Exp nativeHeat112Coef nativeHeat112Fixed nativeHeat112Init nativeHeat112Base nativeHeatStep_hOld_112_Gen
    nativeHeatStep_hFr_112_Gen nativeHeatStep_hArg_112_Gen nativeHeatStep_hExp_112_Gen
    nativeHeatStep_hCoef_112_Gen nativeHeatStep_hFixed_112_Gen
    nativeHeatStep_hInit_112_Gen nativeHeatStep_hBase_112_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_112_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_112_Gen :
    nativeHeatY0Gen 112 = nativeShiftedFrame 1 (min nativeGap113Old.x nativeGap113Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_112_Gen, nativeHeatStep_hInd_112_Gen]

theorem nativeHeatStepFrameNum_112_Gen : NativeHeatStepFrameNum 112 := by
  have h1 := nativeHeatStep_hOld_112_Gen
  have h2 := nativeHeatStep_hInd_112_Gen
  have h3 := nativeHeatStep_hVar_112_Gen
  have h4 := nativeHeatStep_hQm_112_Gen
  have h5 := nativeHeatStep_hQN_112_Gen
  have h6 := nativeHeatStep_hY0_112_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_112_Gen : NativeHeatStepIndivNum 112 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 112 (by norm_num)) = nativeGap113Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_112_Gen]; exact nativeGap113Old_source
  · rw [hc, nativeHeatStep_hInd_112_Gen]; exact nativeGap113Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_112_Gen : nativeHeatY48Gen 112 = nativeHeat112Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_112_Gen, nativeHeatStep_hFr_112_Gen,
    nativeHeatStep_hCoef_112_Gen, nativeHeatStep_hFixed_112_Gen,
    nativeHeatStep_hBase_112_Gen]
  exact nativeHeat112All48

theorem nativeHeatResultGen_112 : nativeHeatResultGen 112 = nativeHeat112Result := by
  rw [← nativeHeat112Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_112_Gen, nativeHeatStep_hY0_112_Gen, nativeHeatStep_hExp_112_Gen,
    nativeHeatStep_hInit_112_Gen, nativeHeatStep_hFixed_112_Gen]

end ASDExplicitGamma.Native

end
