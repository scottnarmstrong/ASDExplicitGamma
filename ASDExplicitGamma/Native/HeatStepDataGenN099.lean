module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat099Complete
public import ASDExplicitGamma.Numerics.Native.Gap100Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_099_Gen : nativeHeatOldRowGen 99 = nativeGap100Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_099_Gen : nativeHeatIndividualGen 99 = nativeGap100Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_099_Gen : nativeHeatGenVariance 99 = nativeHeat099Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_099_Gen, nativeHeat099Variance_formula]

theorem nativeHeatStep_hSpec_099_Gen : nativeHeatGenSpectral 99 = nativeHeat099Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_099_Gen, nativeHeat099Variance_formula]

theorem nativeHeatStep_hQm_099_Gen : nativeHeatGenQm 99 = nativeHeat099Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_099_Gen, nativeHeatStep_hSpec_099_Gen,
    nativeHeat099Qm_formula]

theorem nativeHeatStep_hQN_099_Gen : nativeHeatQNGen 99 = nativeHeat099QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_099_Gen, nativeHeat099QN_formula]

theorem nativeHeatStep_hFr_099_Gen : nativeHeatFramesGen 99 = nativeHeat099Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_099_Gen, nativeHeatStep_hInd_099_Gen,
    nativeHeatStep_hVar_099_Gen, nativeHeatStep_hQN_099_Gen, nativeHeat099Frames_formula]

theorem nativeHeatStep_hArg_099_Gen : nativeHeatExpArgGen 99 = nativeHeatExpArg nativeGap100Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_099_Gen]

theorem nativeHeatStep_hExp_099_Gen : nativeHeatExpGen 99 = nativeHeat099Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_099_Gen, nativeHeat099Exp_formula]

theorem nativeHeatStep_hCoef_099_Gen : nativeHeatCoefGen 99 = nativeHeat099Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_099_Gen, nativeHeat099Coef_formula]

theorem nativeHeatStep_hInit_099_Gen : nativeHeatInitGen 99 = nativeHeat099Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_099_Gen, nativeHeatStep_hVar_099_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat099Init00_formula
    · exact nativeHeat099Init01_formula
    · exact nativeHeat099Init02_formula
    · exact nativeHeat099Init03_formula
    · exact nativeHeat099Init04_formula
    · exact nativeHeat099Init05_formula
    · exact nativeHeat099Init06_formula
    · exact nativeHeat099Init07_formula
    · exact nativeHeat099Init08_formula
    · exact nativeHeat099Init09_formula
    · exact nativeHeat099Init10_formula
    · exact nativeHeat099Init11_formula
    · exact nativeHeat099Init12_formula
    · exact nativeHeat099Init13_formula
    · exact nativeHeat099Init14_formula
    · exact nativeHeat099Init15_formula
    · exact nativeHeat099Init16_formula
    · exact nativeHeat099Init17_formula
    · exact nativeHeat099Init18_formula
    · exact nativeHeat099Init19_formula
    · exact nativeHeat099Init20_formula
theorem nativeHeatStep_hBase_099_Gen : nativeHeatBaseGen 99 = nativeHeat099Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_099_Gen, nativeHeatStep_hInit_099_Gen, nativeHeat099Base_formula]

theorem nativeHeatStep_hFixed_099_Gen : nativeHeatFixedGen 99 = nativeHeat099Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_099_Gen, nativeHeatStep_hFr_099_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat099Fixed01_formula
    · exact nativeHeat099Fixed02_formula
    · exact nativeHeat099Fixed03_formula
    · exact nativeHeat099Fixed04_formula
    · exact nativeHeat099Fixed05_formula
    · exact nativeHeat099Fixed06_formula
    · exact nativeHeat099Fixed07_formula
    · exact nativeHeat099Fixed08_formula
    · exact nativeHeat099Fixed09_formula
    · exact nativeHeat099Fixed10_formula
    · exact nativeHeat099Fixed11_formula
    · exact nativeHeat099Fixed12_formula
    · exact nativeHeat099Fixed13_formula
    · exact nativeHeat099Fixed14_formula
    · exact nativeHeat099Fixed15_formula
    · exact nativeHeat099Fixed16_formula
    · exact nativeHeat099Fixed17_formula
    · exact nativeHeat099Fixed18_formula
    · exact nativeHeat099Fixed19_formula
    · exact nativeHeat099Fixed20_formula

theorem nativeHeatStep_chk_099_Gen :
    nativeHeatPassRootsOk nativeGap100Old nativeHeat099Frames nativeHeat099Coef nativeHeat099Fixed nativeHeat099Base 48 nativeHeat099Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_099_Gen : NativeHeatStepPassNum 99 := by
  refine nativeHeatStepPassNum_of_literals 99 nativeGap100Old nativeHeat099Frames (nativeHeatExpArg nativeGap100Old)
    nativeHeat099Exp nativeHeat099Coef nativeHeat099Fixed nativeHeat099Init nativeHeat099Base nativeHeatStep_hOld_099_Gen
    nativeHeatStep_hFr_099_Gen nativeHeatStep_hArg_099_Gen nativeHeatStep_hExp_099_Gen
    nativeHeatStep_hCoef_099_Gen nativeHeatStep_hFixed_099_Gen
    nativeHeatStep_hInit_099_Gen nativeHeatStep_hBase_099_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_099_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_099_Gen :
    nativeHeatY0Gen 99 = nativeShiftedFrame 1 (min nativeGap100Old.x nativeGap100Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_099_Gen, nativeHeatStep_hInd_099_Gen]

theorem nativeHeatStepFrameNum_099_Gen : NativeHeatStepFrameNum 99 := by
  have h1 := nativeHeatStep_hOld_099_Gen
  have h2 := nativeHeatStep_hInd_099_Gen
  have h3 := nativeHeatStep_hVar_099_Gen
  have h4 := nativeHeatStep_hQm_099_Gen
  have h5 := nativeHeatStep_hQN_099_Gen
  have h6 := nativeHeatStep_hY0_099_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_099_Gen : NativeHeatStepIndivNum 99 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 99 (by norm_num)) = nativeGap100Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_099_Gen]; exact nativeGap100Old_source
  · rw [hc, nativeHeatStep_hInd_099_Gen]; exact nativeGap100Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_099_Gen : nativeHeatY48Gen 99 = nativeHeat099Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_099_Gen, nativeHeatStep_hFr_099_Gen,
    nativeHeatStep_hCoef_099_Gen, nativeHeatStep_hFixed_099_Gen,
    nativeHeatStep_hBase_099_Gen]
  exact nativeHeat099All48

theorem nativeHeatResultGen_099 : nativeHeatResultGen 99 = nativeHeat099Result := by
  rw [← nativeHeat099Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_099_Gen, nativeHeatStep_hY0_099_Gen, nativeHeatStep_hExp_099_Gen,
    nativeHeatStep_hInit_099_Gen, nativeHeatStep_hFixed_099_Gen]

end ASDExplicitGamma.Native

end
