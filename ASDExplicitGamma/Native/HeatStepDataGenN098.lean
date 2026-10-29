module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat098Complete
public import ASDExplicitGamma.Numerics.Native.Gap099Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_098_Gen : nativeHeatOldRowGen 98 = nativeGap099Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_098_Gen : nativeHeatIndividualGen 98 = nativeGap099Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_098_Gen : nativeHeatGenVariance 98 = nativeHeat098Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_098_Gen, nativeHeat098Variance_formula]

theorem nativeHeatStep_hSpec_098_Gen : nativeHeatGenSpectral 98 = nativeHeat098Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_098_Gen, nativeHeat098Variance_formula]

theorem nativeHeatStep_hQm_098_Gen : nativeHeatGenQm 98 = nativeHeat098Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_098_Gen, nativeHeatStep_hSpec_098_Gen,
    nativeHeat098Qm_formula]

theorem nativeHeatStep_hQN_098_Gen : nativeHeatQNGen 98 = nativeHeat098QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_098_Gen, nativeHeat098QN_formula]

theorem nativeHeatStep_hFr_098_Gen : nativeHeatFramesGen 98 = nativeHeat098Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_098_Gen, nativeHeatStep_hInd_098_Gen,
    nativeHeatStep_hVar_098_Gen, nativeHeatStep_hQN_098_Gen, nativeHeat098Frames_formula]

theorem nativeHeatStep_hArg_098_Gen : nativeHeatExpArgGen 98 = nativeHeatExpArg nativeGap099Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_098_Gen]

theorem nativeHeatStep_hExp_098_Gen : nativeHeatExpGen 98 = nativeHeat098Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_098_Gen, nativeHeat098Exp_formula]

theorem nativeHeatStep_hCoef_098_Gen : nativeHeatCoefGen 98 = nativeHeat098Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_098_Gen, nativeHeat098Coef_formula]

theorem nativeHeatStep_hInit_098_Gen : nativeHeatInitGen 98 = nativeHeat098Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_098_Gen, nativeHeatStep_hVar_098_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat098Init00_formula
    · exact nativeHeat098Init01_formula
    · exact nativeHeat098Init02_formula
    · exact nativeHeat098Init03_formula
    · exact nativeHeat098Init04_formula
    · exact nativeHeat098Init05_formula
    · exact nativeHeat098Init06_formula
    · exact nativeHeat098Init07_formula
    · exact nativeHeat098Init08_formula
    · exact nativeHeat098Init09_formula
    · exact nativeHeat098Init10_formula
    · exact nativeHeat098Init11_formula
    · exact nativeHeat098Init12_formula
    · exact nativeHeat098Init13_formula
    · exact nativeHeat098Init14_formula
    · exact nativeHeat098Init15_formula
    · exact nativeHeat098Init16_formula
    · exact nativeHeat098Init17_formula
    · exact nativeHeat098Init18_formula
    · exact nativeHeat098Init19_formula
    · exact nativeHeat098Init20_formula
theorem nativeHeatStep_hBase_098_Gen : nativeHeatBaseGen 98 = nativeHeat098Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_098_Gen, nativeHeatStep_hInit_098_Gen, nativeHeat098Base_formula]

theorem nativeHeatStep_hFixed_098_Gen : nativeHeatFixedGen 98 = nativeHeat098Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_098_Gen, nativeHeatStep_hFr_098_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat098Fixed01_formula
    · exact nativeHeat098Fixed02_formula
    · exact nativeHeat098Fixed03_formula
    · exact nativeHeat098Fixed04_formula
    · exact nativeHeat098Fixed05_formula
    · exact nativeHeat098Fixed06_formula
    · exact nativeHeat098Fixed07_formula
    · exact nativeHeat098Fixed08_formula
    · exact nativeHeat098Fixed09_formula
    · exact nativeHeat098Fixed10_formula
    · exact nativeHeat098Fixed11_formula
    · exact nativeHeat098Fixed12_formula
    · exact nativeHeat098Fixed13_formula
    · exact nativeHeat098Fixed14_formula
    · exact nativeHeat098Fixed15_formula
    · exact nativeHeat098Fixed16_formula
    · exact nativeHeat098Fixed17_formula
    · exact nativeHeat098Fixed18_formula
    · exact nativeHeat098Fixed19_formula
    · exact nativeHeat098Fixed20_formula

theorem nativeHeatStep_chk_098_Gen :
    nativeHeatPassRootsOk nativeGap099Old nativeHeat098Frames nativeHeat098Coef nativeHeat098Fixed nativeHeat098Base 48 nativeHeat098Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_098_Gen : NativeHeatStepPassNum 98 := by
  refine nativeHeatStepPassNum_of_literals 98 nativeGap099Old nativeHeat098Frames (nativeHeatExpArg nativeGap099Old)
    nativeHeat098Exp nativeHeat098Coef nativeHeat098Fixed nativeHeat098Init nativeHeat098Base nativeHeatStep_hOld_098_Gen
    nativeHeatStep_hFr_098_Gen nativeHeatStep_hArg_098_Gen nativeHeatStep_hExp_098_Gen
    nativeHeatStep_hCoef_098_Gen nativeHeatStep_hFixed_098_Gen
    nativeHeatStep_hInit_098_Gen nativeHeatStep_hBase_098_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_098_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_098_Gen :
    nativeHeatY0Gen 98 = nativeShiftedFrame 1 (min nativeGap099Old.x nativeGap099Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_098_Gen, nativeHeatStep_hInd_098_Gen]

theorem nativeHeatStepFrameNum_098_Gen : NativeHeatStepFrameNum 98 := by
  have h1 := nativeHeatStep_hOld_098_Gen
  have h2 := nativeHeatStep_hInd_098_Gen
  have h3 := nativeHeatStep_hVar_098_Gen
  have h4 := nativeHeatStep_hQm_098_Gen
  have h5 := nativeHeatStep_hQN_098_Gen
  have h6 := nativeHeatStep_hY0_098_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_098_Gen : NativeHeatStepIndivNum 98 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 98 (by norm_num)) = nativeGap099Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_098_Gen]; exact nativeGap099Old_source
  · rw [hc, nativeHeatStep_hInd_098_Gen]; exact nativeGap099Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_098_Gen : nativeHeatY48Gen 98 = nativeHeat098Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_098_Gen, nativeHeatStep_hFr_098_Gen,
    nativeHeatStep_hCoef_098_Gen, nativeHeatStep_hFixed_098_Gen,
    nativeHeatStep_hBase_098_Gen]
  exact nativeHeat098All48

theorem nativeHeatResultGen_098 : nativeHeatResultGen 98 = nativeHeat098Result := by
  rw [← nativeHeat098Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_098_Gen, nativeHeatStep_hY0_098_Gen, nativeHeatStep_hExp_098_Gen,
    nativeHeatStep_hInit_098_Gen, nativeHeatStep_hFixed_098_Gen]

end ASDExplicitGamma.Native

end
