module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat060Complete
public import ASDExplicitGamma.Numerics.Native.Gap061Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_060_Gen : nativeHeatOldRowGen 60 = nativeGap061Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_060_Gen : nativeHeatIndividualGen 60 = nativeGap061Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_060_Gen : nativeHeatGenVariance 60 = nativeHeat060Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_060_Gen, nativeHeat060Variance_formula]

theorem nativeHeatStep_hSpec_060_Gen : nativeHeatGenSpectral 60 = nativeHeat060Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_060_Gen, nativeHeat060Variance_formula]

theorem nativeHeatStep_hQm_060_Gen : nativeHeatGenQm 60 = nativeHeat060Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_060_Gen, nativeHeatStep_hSpec_060_Gen,
    nativeHeat060Qm_formula]

theorem nativeHeatStep_hQN_060_Gen : nativeHeatQNGen 60 = nativeHeat060QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_060_Gen, nativeHeat060QN_formula]

theorem nativeHeatStep_hFr_060_Gen : nativeHeatFramesGen 60 = nativeHeat060Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_060_Gen, nativeHeatStep_hInd_060_Gen,
    nativeHeatStep_hVar_060_Gen, nativeHeatStep_hQN_060_Gen, nativeHeat060Frames_formula]

theorem nativeHeatStep_hArg_060_Gen : nativeHeatExpArgGen 60 = nativeHeatExpArg nativeGap061Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_060_Gen]

theorem nativeHeatStep_hExp_060_Gen : nativeHeatExpGen 60 = nativeHeat060Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_060_Gen, nativeHeat060Exp_formula]

theorem nativeHeatStep_hCoef_060_Gen : nativeHeatCoefGen 60 = nativeHeat060Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_060_Gen, nativeHeat060Coef_formula]

theorem nativeHeatStep_hInit_060_Gen : nativeHeatInitGen 60 = nativeHeat060Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_060_Gen, nativeHeatStep_hVar_060_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat060Init00_formula
    · exact nativeHeat060Init01_formula
    · exact nativeHeat060Init02_formula
    · exact nativeHeat060Init03_formula
    · exact nativeHeat060Init04_formula
    · exact nativeHeat060Init05_formula
    · exact nativeHeat060Init06_formula
    · exact nativeHeat060Init07_formula
    · exact nativeHeat060Init08_formula
    · exact nativeHeat060Init09_formula
    · exact nativeHeat060Init10_formula
    · exact nativeHeat060Init11_formula
    · exact nativeHeat060Init12_formula
    · exact nativeHeat060Init13_formula
    · exact nativeHeat060Init14_formula
    · exact nativeHeat060Init15_formula
    · exact nativeHeat060Init16_formula
    · exact nativeHeat060Init17_formula
    · exact nativeHeat060Init18_formula
    · exact nativeHeat060Init19_formula
    · exact nativeHeat060Init20_formula
theorem nativeHeatStep_hBase_060_Gen : nativeHeatBaseGen 60 = nativeHeat060Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_060_Gen, nativeHeatStep_hInit_060_Gen, nativeHeat060Base_formula]

theorem nativeHeatStep_hFixed_060_Gen : nativeHeatFixedGen 60 = nativeHeat060Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_060_Gen, nativeHeatStep_hFr_060_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat060Fixed01_formula
    · exact nativeHeat060Fixed02_formula
    · exact nativeHeat060Fixed03_formula
    · exact nativeHeat060Fixed04_formula
    · exact nativeHeat060Fixed05_formula
    · exact nativeHeat060Fixed06_formula
    · exact nativeHeat060Fixed07_formula
    · exact nativeHeat060Fixed08_formula
    · exact nativeHeat060Fixed09_formula
    · exact nativeHeat060Fixed10_formula
    · exact nativeHeat060Fixed11_formula
    · exact nativeHeat060Fixed12_formula
    · exact nativeHeat060Fixed13_formula
    · exact nativeHeat060Fixed14_formula
    · exact nativeHeat060Fixed15_formula
    · exact nativeHeat060Fixed16_formula
    · exact nativeHeat060Fixed17_formula
    · exact nativeHeat060Fixed18_formula
    · exact nativeHeat060Fixed19_formula
    · exact nativeHeat060Fixed20_formula

theorem nativeHeatStep_chk_060_Gen :
    nativeHeatPassRootsOk nativeGap061Old nativeHeat060Frames nativeHeat060Coef nativeHeat060Fixed nativeHeat060Base 48 nativeHeat060Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_060_Gen : NativeHeatStepPassNum 60 := by
  refine nativeHeatStepPassNum_of_literals 60 nativeGap061Old nativeHeat060Frames (nativeHeatExpArg nativeGap061Old)
    nativeHeat060Exp nativeHeat060Coef nativeHeat060Fixed nativeHeat060Init nativeHeat060Base nativeHeatStep_hOld_060_Gen
    nativeHeatStep_hFr_060_Gen nativeHeatStep_hArg_060_Gen nativeHeatStep_hExp_060_Gen
    nativeHeatStep_hCoef_060_Gen nativeHeatStep_hFixed_060_Gen
    nativeHeatStep_hInit_060_Gen nativeHeatStep_hBase_060_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_060_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_060_Gen :
    nativeHeatY0Gen 60 = nativeShiftedFrame 1 (min nativeGap061Old.x nativeGap061Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_060_Gen, nativeHeatStep_hInd_060_Gen]

theorem nativeHeatStepFrameNum_060_Gen : NativeHeatStepFrameNum 60 := by
  have h1 := nativeHeatStep_hOld_060_Gen
  have h2 := nativeHeatStep_hInd_060_Gen
  have h3 := nativeHeatStep_hVar_060_Gen
  have h4 := nativeHeatStep_hQm_060_Gen
  have h5 := nativeHeatStep_hQN_060_Gen
  have h6 := nativeHeatStep_hY0_060_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_060_Gen : NativeHeatStepIndivNum 60 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 60 (by norm_num)) = nativeGap061Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_060_Gen]; exact nativeGap061Old_source
  · rw [hc, nativeHeatStep_hInd_060_Gen]; exact nativeGap061Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_060_Gen : nativeHeatY48Gen 60 = nativeHeat060Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_060_Gen, nativeHeatStep_hFr_060_Gen,
    nativeHeatStep_hCoef_060_Gen, nativeHeatStep_hFixed_060_Gen,
    nativeHeatStep_hBase_060_Gen]
  exact nativeHeat060All48

theorem nativeHeatResultGen_060 : nativeHeatResultGen 60 = nativeHeat060Result := by
  rw [← nativeHeat060Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_060_Gen, nativeHeatStep_hY0_060_Gen, nativeHeatStep_hExp_060_Gen,
    nativeHeatStep_hInit_060_Gen, nativeHeatStep_hFixed_060_Gen]

end ASDExplicitGamma.Native

end
