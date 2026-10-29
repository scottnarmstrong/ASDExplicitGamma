module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat086Complete
public import ASDExplicitGamma.Numerics.Native.Gap087Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_086_Gen : nativeHeatOldRowGen 86 = nativeGap087Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_086_Gen : nativeHeatIndividualGen 86 = nativeGap087Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_086_Gen : nativeHeatGenVariance 86 = nativeHeat086Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_086_Gen, nativeHeat086Variance_formula]

theorem nativeHeatStep_hSpec_086_Gen : nativeHeatGenSpectral 86 = nativeHeat086Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_086_Gen, nativeHeat086Variance_formula]

theorem nativeHeatStep_hQm_086_Gen : nativeHeatGenQm 86 = nativeHeat086Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_086_Gen, nativeHeatStep_hSpec_086_Gen,
    nativeHeat086Qm_formula]

theorem nativeHeatStep_hQN_086_Gen : nativeHeatQNGen 86 = nativeHeat086QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_086_Gen, nativeHeat086QN_formula]

theorem nativeHeatStep_hFr_086_Gen : nativeHeatFramesGen 86 = nativeHeat086Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_086_Gen, nativeHeatStep_hInd_086_Gen,
    nativeHeatStep_hVar_086_Gen, nativeHeatStep_hQN_086_Gen, nativeHeat086Frames_formula]

theorem nativeHeatStep_hArg_086_Gen : nativeHeatExpArgGen 86 = nativeHeatExpArg nativeGap087Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_086_Gen]

theorem nativeHeatStep_hExp_086_Gen : nativeHeatExpGen 86 = nativeHeat086Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_086_Gen, nativeHeat086Exp_formula]

theorem nativeHeatStep_hCoef_086_Gen : nativeHeatCoefGen 86 = nativeHeat086Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_086_Gen, nativeHeat086Coef_formula]

theorem nativeHeatStep_hInit_086_Gen : nativeHeatInitGen 86 = nativeHeat086Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_086_Gen, nativeHeatStep_hVar_086_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat086Init00_formula
    · exact nativeHeat086Init01_formula
    · exact nativeHeat086Init02_formula
    · exact nativeHeat086Init03_formula
    · exact nativeHeat086Init04_formula
    · exact nativeHeat086Init05_formula
    · exact nativeHeat086Init06_formula
    · exact nativeHeat086Init07_formula
    · exact nativeHeat086Init08_formula
    · exact nativeHeat086Init09_formula
    · exact nativeHeat086Init10_formula
    · exact nativeHeat086Init11_formula
    · exact nativeHeat086Init12_formula
    · exact nativeHeat086Init13_formula
    · exact nativeHeat086Init14_formula
    · exact nativeHeat086Init15_formula
    · exact nativeHeat086Init16_formula
    · exact nativeHeat086Init17_formula
    · exact nativeHeat086Init18_formula
    · exact nativeHeat086Init19_formula
    · exact nativeHeat086Init20_formula
theorem nativeHeatStep_hBase_086_Gen : nativeHeatBaseGen 86 = nativeHeat086Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_086_Gen, nativeHeatStep_hInit_086_Gen, nativeHeat086Base_formula]

theorem nativeHeatStep_hFixed_086_Gen : nativeHeatFixedGen 86 = nativeHeat086Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_086_Gen, nativeHeatStep_hFr_086_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat086Fixed01_formula
    · exact nativeHeat086Fixed02_formula
    · exact nativeHeat086Fixed03_formula
    · exact nativeHeat086Fixed04_formula
    · exact nativeHeat086Fixed05_formula
    · exact nativeHeat086Fixed06_formula
    · exact nativeHeat086Fixed07_formula
    · exact nativeHeat086Fixed08_formula
    · exact nativeHeat086Fixed09_formula
    · exact nativeHeat086Fixed10_formula
    · exact nativeHeat086Fixed11_formula
    · exact nativeHeat086Fixed12_formula
    · exact nativeHeat086Fixed13_formula
    · exact nativeHeat086Fixed14_formula
    · exact nativeHeat086Fixed15_formula
    · exact nativeHeat086Fixed16_formula
    · exact nativeHeat086Fixed17_formula
    · exact nativeHeat086Fixed18_formula
    · exact nativeHeat086Fixed19_formula
    · exact nativeHeat086Fixed20_formula

theorem nativeHeatStep_chk_086_Gen :
    nativeHeatPassRootsOk nativeGap087Old nativeHeat086Frames nativeHeat086Coef nativeHeat086Fixed nativeHeat086Base 48 nativeHeat086Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_086_Gen : NativeHeatStepPassNum 86 := by
  refine nativeHeatStepPassNum_of_literals 86 nativeGap087Old nativeHeat086Frames (nativeHeatExpArg nativeGap087Old)
    nativeHeat086Exp nativeHeat086Coef nativeHeat086Fixed nativeHeat086Init nativeHeat086Base nativeHeatStep_hOld_086_Gen
    nativeHeatStep_hFr_086_Gen nativeHeatStep_hArg_086_Gen nativeHeatStep_hExp_086_Gen
    nativeHeatStep_hCoef_086_Gen nativeHeatStep_hFixed_086_Gen
    nativeHeatStep_hInit_086_Gen nativeHeatStep_hBase_086_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_086_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_086_Gen :
    nativeHeatY0Gen 86 = nativeShiftedFrame 1 (min nativeGap087Old.x nativeGap087Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_086_Gen, nativeHeatStep_hInd_086_Gen]

theorem nativeHeatStepFrameNum_086_Gen : NativeHeatStepFrameNum 86 := by
  have h1 := nativeHeatStep_hOld_086_Gen
  have h2 := nativeHeatStep_hInd_086_Gen
  have h3 := nativeHeatStep_hVar_086_Gen
  have h4 := nativeHeatStep_hQm_086_Gen
  have h5 := nativeHeatStep_hQN_086_Gen
  have h6 := nativeHeatStep_hY0_086_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_086_Gen : NativeHeatStepIndivNum 86 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 86 (by norm_num)) = nativeGap087Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_086_Gen]; exact nativeGap087Old_source
  · rw [hc, nativeHeatStep_hInd_086_Gen]; exact nativeGap087Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_086_Gen : nativeHeatY48Gen 86 = nativeHeat086Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_086_Gen, nativeHeatStep_hFr_086_Gen,
    nativeHeatStep_hCoef_086_Gen, nativeHeatStep_hFixed_086_Gen,
    nativeHeatStep_hBase_086_Gen]
  exact nativeHeat086All48

theorem nativeHeatResultGen_086 : nativeHeatResultGen 86 = nativeHeat086Result := by
  rw [← nativeHeat086Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_086_Gen, nativeHeatStep_hY0_086_Gen, nativeHeatStep_hExp_086_Gen,
    nativeHeatStep_hInit_086_Gen, nativeHeatStep_hFixed_086_Gen]

end ASDExplicitGamma.Native

end
