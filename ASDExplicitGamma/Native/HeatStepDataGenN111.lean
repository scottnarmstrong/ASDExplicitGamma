module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat111Complete
public import ASDExplicitGamma.Numerics.Native.Gap112Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_111_Gen : nativeHeatOldRowGen 111 = nativeGap112Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_111_Gen : nativeHeatIndividualGen 111 = nativeGap112Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_111_Gen : nativeHeatGenVariance 111 = nativeHeat111Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_111_Gen, nativeHeat111Variance_formula]

theorem nativeHeatStep_hSpec_111_Gen : nativeHeatGenSpectral 111 = nativeHeat111Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_111_Gen, nativeHeat111Variance_formula]

theorem nativeHeatStep_hQm_111_Gen : nativeHeatGenQm 111 = nativeHeat111Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_111_Gen, nativeHeatStep_hSpec_111_Gen,
    nativeHeat111Qm_formula]

theorem nativeHeatStep_hQN_111_Gen : nativeHeatQNGen 111 = nativeHeat111QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_111_Gen, nativeHeat111QN_formula]

theorem nativeHeatStep_hFr_111_Gen : nativeHeatFramesGen 111 = nativeHeat111Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_111_Gen, nativeHeatStep_hInd_111_Gen,
    nativeHeatStep_hVar_111_Gen, nativeHeatStep_hQN_111_Gen, nativeHeat111Frames_formula]

theorem nativeHeatStep_hArg_111_Gen : nativeHeatExpArgGen 111 = nativeHeatExpArg nativeGap112Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_111_Gen]

theorem nativeHeatStep_hExp_111_Gen : nativeHeatExpGen 111 = nativeHeat111Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_111_Gen, nativeHeat111Exp_formula]

theorem nativeHeatStep_hCoef_111_Gen : nativeHeatCoefGen 111 = nativeHeat111Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_111_Gen, nativeHeat111Coef_formula]

theorem nativeHeatStep_hInit_111_Gen : nativeHeatInitGen 111 = nativeHeat111Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_111_Gen, nativeHeatStep_hVar_111_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat111Init00_formula
    · exact nativeHeat111Init01_formula
    · exact nativeHeat111Init02_formula
    · exact nativeHeat111Init03_formula
    · exact nativeHeat111Init04_formula
    · exact nativeHeat111Init05_formula
    · exact nativeHeat111Init06_formula
    · exact nativeHeat111Init07_formula
    · exact nativeHeat111Init08_formula
    · exact nativeHeat111Init09_formula
    · exact nativeHeat111Init10_formula
    · exact nativeHeat111Init11_formula
    · exact nativeHeat111Init12_formula
    · exact nativeHeat111Init13_formula
    · exact nativeHeat111Init14_formula
    · exact nativeHeat111Init15_formula
    · exact nativeHeat111Init16_formula
    · exact nativeHeat111Init17_formula
    · exact nativeHeat111Init18_formula
    · exact nativeHeat111Init19_formula
    · exact nativeHeat111Init20_formula
theorem nativeHeatStep_hBase_111_Gen : nativeHeatBaseGen 111 = nativeHeat111Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_111_Gen, nativeHeatStep_hInit_111_Gen, nativeHeat111Base_formula]

theorem nativeHeatStep_hFixed_111_Gen : nativeHeatFixedGen 111 = nativeHeat111Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_111_Gen, nativeHeatStep_hFr_111_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat111Fixed01_formula
    · exact nativeHeat111Fixed02_formula
    · exact nativeHeat111Fixed03_formula
    · exact nativeHeat111Fixed04_formula
    · exact nativeHeat111Fixed05_formula
    · exact nativeHeat111Fixed06_formula
    · exact nativeHeat111Fixed07_formula
    · exact nativeHeat111Fixed08_formula
    · exact nativeHeat111Fixed09_formula
    · exact nativeHeat111Fixed10_formula
    · exact nativeHeat111Fixed11_formula
    · exact nativeHeat111Fixed12_formula
    · exact nativeHeat111Fixed13_formula
    · exact nativeHeat111Fixed14_formula
    · exact nativeHeat111Fixed15_formula
    · exact nativeHeat111Fixed16_formula
    · exact nativeHeat111Fixed17_formula
    · exact nativeHeat111Fixed18_formula
    · exact nativeHeat111Fixed19_formula
    · exact nativeHeat111Fixed20_formula

theorem nativeHeatStep_chk_111_Gen :
    nativeHeatPassRootsOk nativeGap112Old nativeHeat111Frames nativeHeat111Coef nativeHeat111Fixed nativeHeat111Base 48 nativeHeat111Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_111_Gen : NativeHeatStepPassNum 111 := by
  refine nativeHeatStepPassNum_of_literals 111 nativeGap112Old nativeHeat111Frames (nativeHeatExpArg nativeGap112Old)
    nativeHeat111Exp nativeHeat111Coef nativeHeat111Fixed nativeHeat111Init nativeHeat111Base nativeHeatStep_hOld_111_Gen
    nativeHeatStep_hFr_111_Gen nativeHeatStep_hArg_111_Gen nativeHeatStep_hExp_111_Gen
    nativeHeatStep_hCoef_111_Gen nativeHeatStep_hFixed_111_Gen
    nativeHeatStep_hInit_111_Gen nativeHeatStep_hBase_111_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_111_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_111_Gen :
    nativeHeatY0Gen 111 = nativeShiftedFrame 1 (min nativeGap112Old.x nativeGap112Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_111_Gen, nativeHeatStep_hInd_111_Gen]

theorem nativeHeatStepFrameNum_111_Gen : NativeHeatStepFrameNum 111 := by
  have h1 := nativeHeatStep_hOld_111_Gen
  have h2 := nativeHeatStep_hInd_111_Gen
  have h3 := nativeHeatStep_hVar_111_Gen
  have h4 := nativeHeatStep_hQm_111_Gen
  have h5 := nativeHeatStep_hQN_111_Gen
  have h6 := nativeHeatStep_hY0_111_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_111_Gen : NativeHeatStepIndivNum 111 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 111 (by norm_num)) = nativeGap112Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_111_Gen]; exact nativeGap112Old_source
  · rw [hc, nativeHeatStep_hInd_111_Gen]; exact nativeGap112Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_111_Gen : nativeHeatY48Gen 111 = nativeHeat111Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_111_Gen, nativeHeatStep_hFr_111_Gen,
    nativeHeatStep_hCoef_111_Gen, nativeHeatStep_hFixed_111_Gen,
    nativeHeatStep_hBase_111_Gen]
  exact nativeHeat111All48

theorem nativeHeatResultGen_111 : nativeHeatResultGen 111 = nativeHeat111Result := by
  rw [← nativeHeat111Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_111_Gen, nativeHeatStep_hY0_111_Gen, nativeHeatStep_hExp_111_Gen,
    nativeHeatStep_hInit_111_Gen, nativeHeatStep_hFixed_111_Gen]

end ASDExplicitGamma.Native

end
