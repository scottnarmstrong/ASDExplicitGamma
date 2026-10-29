module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat141Complete
public import ASDExplicitGamma.Numerics.Native.Gap142Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_141_Gen : nativeHeatOldRowGen 141 = nativeGap142Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_141_Gen : nativeHeatIndividualGen 141 = nativeGap142Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_141_Gen : nativeHeatGenVariance 141 = nativeHeat141Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_141_Gen, nativeHeat141Variance_formula]

theorem nativeHeatStep_hSpec_141_Gen : nativeHeatGenSpectral 141 = nativeHeat141Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_141_Gen, nativeHeat141Variance_formula]

theorem nativeHeatStep_hQm_141_Gen : nativeHeatGenQm 141 = nativeHeat141Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_141_Gen, nativeHeatStep_hSpec_141_Gen,
    nativeHeat141Qm_formula]

theorem nativeHeatStep_hQN_141_Gen : nativeHeatQNGen 141 = nativeHeat141QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_141_Gen, nativeHeat141QN_formula]

theorem nativeHeatStep_hFr_141_Gen : nativeHeatFramesGen 141 = nativeHeat141Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_141_Gen, nativeHeatStep_hInd_141_Gen,
    nativeHeatStep_hVar_141_Gen, nativeHeatStep_hQN_141_Gen, nativeHeat141Frames_formula]

theorem nativeHeatStep_hArg_141_Gen : nativeHeatExpArgGen 141 = nativeHeatExpArg nativeGap142Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_141_Gen]

theorem nativeHeatStep_hExp_141_Gen : nativeHeatExpGen 141 = nativeHeat141Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_141_Gen, nativeHeat141Exp_formula]

theorem nativeHeatStep_hCoef_141_Gen : nativeHeatCoefGen 141 = nativeHeat141Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_141_Gen, nativeHeat141Coef_formula]

theorem nativeHeatStep_hInit_141_Gen : nativeHeatInitGen 141 = nativeHeat141Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_141_Gen, nativeHeatStep_hVar_141_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat141Init00_formula
    · exact nativeHeat141Init01_formula
    · exact nativeHeat141Init02_formula
    · exact nativeHeat141Init03_formula
    · exact nativeHeat141Init04_formula
    · exact nativeHeat141Init05_formula
    · exact nativeHeat141Init06_formula
    · exact nativeHeat141Init07_formula
    · exact nativeHeat141Init08_formula
    · exact nativeHeat141Init09_formula
    · exact nativeHeat141Init10_formula
    · exact nativeHeat141Init11_formula
    · exact nativeHeat141Init12_formula
    · exact nativeHeat141Init13_formula
    · exact nativeHeat141Init14_formula
    · exact nativeHeat141Init15_formula
    · exact nativeHeat141Init16_formula
    · exact nativeHeat141Init17_formula
    · exact nativeHeat141Init18_formula
    · exact nativeHeat141Init19_formula
    · exact nativeHeat141Init20_formula
theorem nativeHeatStep_hBase_141_Gen : nativeHeatBaseGen 141 = nativeHeat141Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_141_Gen, nativeHeatStep_hInit_141_Gen, nativeHeat141Base_formula]

theorem nativeHeatStep_hFixed_141_Gen : nativeHeatFixedGen 141 = nativeHeat141Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_141_Gen, nativeHeatStep_hFr_141_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat141Fixed01_formula
    · exact nativeHeat141Fixed02_formula
    · exact nativeHeat141Fixed03_formula
    · exact nativeHeat141Fixed04_formula
    · exact nativeHeat141Fixed05_formula
    · exact nativeHeat141Fixed06_formula
    · exact nativeHeat141Fixed07_formula
    · exact nativeHeat141Fixed08_formula
    · exact nativeHeat141Fixed09_formula
    · exact nativeHeat141Fixed10_formula
    · exact nativeHeat141Fixed11_formula
    · exact nativeHeat141Fixed12_formula
    · exact nativeHeat141Fixed13_formula
    · exact nativeHeat141Fixed14_formula
    · exact nativeHeat141Fixed15_formula
    · exact nativeHeat141Fixed16_formula
    · exact nativeHeat141Fixed17_formula
    · exact nativeHeat141Fixed18_formula
    · exact nativeHeat141Fixed19_formula
    · exact nativeHeat141Fixed20_formula

theorem nativeHeatStep_chk_141_Gen :
    nativeHeatPassRootsOk nativeGap142Old nativeHeat141Frames nativeHeat141Coef nativeHeat141Fixed nativeHeat141Base 48 nativeHeat141Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_141_Gen : NativeHeatStepPassNum 141 := by
  refine nativeHeatStepPassNum_of_literals 141 nativeGap142Old nativeHeat141Frames (nativeHeatExpArg nativeGap142Old)
    nativeHeat141Exp nativeHeat141Coef nativeHeat141Fixed nativeHeat141Init nativeHeat141Base nativeHeatStep_hOld_141_Gen
    nativeHeatStep_hFr_141_Gen nativeHeatStep_hArg_141_Gen nativeHeatStep_hExp_141_Gen
    nativeHeatStep_hCoef_141_Gen nativeHeatStep_hFixed_141_Gen
    nativeHeatStep_hInit_141_Gen nativeHeatStep_hBase_141_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_141_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_141_Gen :
    nativeHeatY0Gen 141 = nativeShiftedFrame 1 (min nativeGap142Old.x nativeGap142Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_141_Gen, nativeHeatStep_hInd_141_Gen]

theorem nativeHeatStepFrameNum_141_Gen : NativeHeatStepFrameNum 141 := by
  have h1 := nativeHeatStep_hOld_141_Gen
  have h2 := nativeHeatStep_hInd_141_Gen
  have h3 := nativeHeatStep_hVar_141_Gen
  have h4 := nativeHeatStep_hQm_141_Gen
  have h5 := nativeHeatStep_hQN_141_Gen
  have h6 := nativeHeatStep_hY0_141_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_141_Gen : NativeHeatStepIndivNum 141 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 141 (by norm_num)) = nativeGap142Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_141_Gen]; exact nativeGap142Old_source
  · rw [hc, nativeHeatStep_hInd_141_Gen]; exact nativeGap142Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_141_Gen : nativeHeatY48Gen 141 = nativeHeat141Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_141_Gen, nativeHeatStep_hFr_141_Gen,
    nativeHeatStep_hCoef_141_Gen, nativeHeatStep_hFixed_141_Gen,
    nativeHeatStep_hBase_141_Gen]
  exact nativeHeat141All48

theorem nativeHeatResultGen_141 : nativeHeatResultGen 141 = nativeHeat141Result := by
  rw [← nativeHeat141Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_141_Gen, nativeHeatStep_hY0_141_Gen, nativeHeatStep_hExp_141_Gen,
    nativeHeatStep_hInit_141_Gen, nativeHeatStep_hFixed_141_Gen]

end ASDExplicitGamma.Native

end
