module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat114Complete
public import ASDExplicitGamma.Numerics.Native.Gap115Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_114_Gen : nativeHeatOldRowGen 114 = nativeGap115Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_114_Gen : nativeHeatIndividualGen 114 = nativeGap115Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_114_Gen : nativeHeatGenVariance 114 = nativeHeat114Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_114_Gen, nativeHeat114Variance_formula]

theorem nativeHeatStep_hSpec_114_Gen : nativeHeatGenSpectral 114 = nativeHeat114Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_114_Gen, nativeHeat114Variance_formula]

theorem nativeHeatStep_hQm_114_Gen : nativeHeatGenQm 114 = nativeHeat114Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_114_Gen, nativeHeatStep_hSpec_114_Gen,
    nativeHeat114Qm_formula]

theorem nativeHeatStep_hQN_114_Gen : nativeHeatQNGen 114 = nativeHeat114QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_114_Gen, nativeHeat114QN_formula]

theorem nativeHeatStep_hFr_114_Gen : nativeHeatFramesGen 114 = nativeHeat114Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_114_Gen, nativeHeatStep_hInd_114_Gen,
    nativeHeatStep_hVar_114_Gen, nativeHeatStep_hQN_114_Gen, nativeHeat114Frames_formula]

theorem nativeHeatStep_hArg_114_Gen : nativeHeatExpArgGen 114 = nativeHeatExpArg nativeGap115Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_114_Gen]

theorem nativeHeatStep_hExp_114_Gen : nativeHeatExpGen 114 = nativeHeat114Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_114_Gen, nativeHeat114Exp_formula]

theorem nativeHeatStep_hCoef_114_Gen : nativeHeatCoefGen 114 = nativeHeat114Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_114_Gen, nativeHeat114Coef_formula]

theorem nativeHeatStep_hInit_114_Gen : nativeHeatInitGen 114 = nativeHeat114Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_114_Gen, nativeHeatStep_hVar_114_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat114Init00_formula
    · exact nativeHeat114Init01_formula
    · exact nativeHeat114Init02_formula
    · exact nativeHeat114Init03_formula
    · exact nativeHeat114Init04_formula
    · exact nativeHeat114Init05_formula
    · exact nativeHeat114Init06_formula
    · exact nativeHeat114Init07_formula
    · exact nativeHeat114Init08_formula
    · exact nativeHeat114Init09_formula
    · exact nativeHeat114Init10_formula
    · exact nativeHeat114Init11_formula
    · exact nativeHeat114Init12_formula
    · exact nativeHeat114Init13_formula
    · exact nativeHeat114Init14_formula
    · exact nativeHeat114Init15_formula
    · exact nativeHeat114Init16_formula
    · exact nativeHeat114Init17_formula
    · exact nativeHeat114Init18_formula
    · exact nativeHeat114Init19_formula
    · exact nativeHeat114Init20_formula
theorem nativeHeatStep_hBase_114_Gen : nativeHeatBaseGen 114 = nativeHeat114Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_114_Gen, nativeHeatStep_hInit_114_Gen, nativeHeat114Base_formula]

theorem nativeHeatStep_hFixed_114_Gen : nativeHeatFixedGen 114 = nativeHeat114Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_114_Gen, nativeHeatStep_hFr_114_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat114Fixed01_formula
    · exact nativeHeat114Fixed02_formula
    · exact nativeHeat114Fixed03_formula
    · exact nativeHeat114Fixed04_formula
    · exact nativeHeat114Fixed05_formula
    · exact nativeHeat114Fixed06_formula
    · exact nativeHeat114Fixed07_formula
    · exact nativeHeat114Fixed08_formula
    · exact nativeHeat114Fixed09_formula
    · exact nativeHeat114Fixed10_formula
    · exact nativeHeat114Fixed11_formula
    · exact nativeHeat114Fixed12_formula
    · exact nativeHeat114Fixed13_formula
    · exact nativeHeat114Fixed14_formula
    · exact nativeHeat114Fixed15_formula
    · exact nativeHeat114Fixed16_formula
    · exact nativeHeat114Fixed17_formula
    · exact nativeHeat114Fixed18_formula
    · exact nativeHeat114Fixed19_formula
    · exact nativeHeat114Fixed20_formula

theorem nativeHeatStep_chk_114_Gen :
    nativeHeatPassRootsOk nativeGap115Old nativeHeat114Frames nativeHeat114Coef nativeHeat114Fixed nativeHeat114Base 48 nativeHeat114Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_114_Gen : NativeHeatStepPassNum 114 := by
  refine nativeHeatStepPassNum_of_literals 114 nativeGap115Old nativeHeat114Frames (nativeHeatExpArg nativeGap115Old)
    nativeHeat114Exp nativeHeat114Coef nativeHeat114Fixed nativeHeat114Init nativeHeat114Base nativeHeatStep_hOld_114_Gen
    nativeHeatStep_hFr_114_Gen nativeHeatStep_hArg_114_Gen nativeHeatStep_hExp_114_Gen
    nativeHeatStep_hCoef_114_Gen nativeHeatStep_hFixed_114_Gen
    nativeHeatStep_hInit_114_Gen nativeHeatStep_hBase_114_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_114_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_114_Gen :
    nativeHeatY0Gen 114 = nativeShiftedFrame 1 (min nativeGap115Old.x nativeGap115Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_114_Gen, nativeHeatStep_hInd_114_Gen]

theorem nativeHeatStepFrameNum_114_Gen : NativeHeatStepFrameNum 114 := by
  have h1 := nativeHeatStep_hOld_114_Gen
  have h2 := nativeHeatStep_hInd_114_Gen
  have h3 := nativeHeatStep_hVar_114_Gen
  have h4 := nativeHeatStep_hQm_114_Gen
  have h5 := nativeHeatStep_hQN_114_Gen
  have h6 := nativeHeatStep_hY0_114_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_114_Gen : NativeHeatStepIndivNum 114 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 114 (by norm_num)) = nativeGap115Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_114_Gen]; exact nativeGap115Old_source
  · rw [hc, nativeHeatStep_hInd_114_Gen]; exact nativeGap115Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_114_Gen : nativeHeatY48Gen 114 = nativeHeat114Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_114_Gen, nativeHeatStep_hFr_114_Gen,
    nativeHeatStep_hCoef_114_Gen, nativeHeatStep_hFixed_114_Gen,
    nativeHeatStep_hBase_114_Gen]
  exact nativeHeat114All48

theorem nativeHeatResultGen_114 : nativeHeatResultGen 114 = nativeHeat114Result := by
  rw [← nativeHeat114Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_114_Gen, nativeHeatStep_hY0_114_Gen, nativeHeatStep_hExp_114_Gen,
    nativeHeatStep_hInit_114_Gen, nativeHeatStep_hFixed_114_Gen]

end ASDExplicitGamma.Native

end
