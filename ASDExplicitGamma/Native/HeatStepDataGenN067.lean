module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat067Complete
public import ASDExplicitGamma.Numerics.Native.Gap068Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_067_Gen : nativeHeatOldRowGen 67 = nativeGap068Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_067_Gen : nativeHeatIndividualGen 67 = nativeGap068Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_067_Gen : nativeHeatGenVariance 67 = nativeHeat067Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_067_Gen, nativeHeat067Variance_formula]

theorem nativeHeatStep_hSpec_067_Gen : nativeHeatGenSpectral 67 = nativeHeat067Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_067_Gen, nativeHeat067Variance_formula]

theorem nativeHeatStep_hQm_067_Gen : nativeHeatGenQm 67 = nativeHeat067Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_067_Gen, nativeHeatStep_hSpec_067_Gen,
    nativeHeat067Qm_formula]

theorem nativeHeatStep_hQN_067_Gen : nativeHeatQNGen 67 = nativeHeat067QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_067_Gen, nativeHeat067QN_formula]

theorem nativeHeatStep_hFr_067_Gen : nativeHeatFramesGen 67 = nativeHeat067Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_067_Gen, nativeHeatStep_hInd_067_Gen,
    nativeHeatStep_hVar_067_Gen, nativeHeatStep_hQN_067_Gen, nativeHeat067Frames_formula]

theorem nativeHeatStep_hArg_067_Gen : nativeHeatExpArgGen 67 = nativeHeatExpArg nativeGap068Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_067_Gen]

theorem nativeHeatStep_hExp_067_Gen : nativeHeatExpGen 67 = nativeHeat067Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_067_Gen, nativeHeat067Exp_formula]

theorem nativeHeatStep_hCoef_067_Gen : nativeHeatCoefGen 67 = nativeHeat067Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_067_Gen, nativeHeat067Coef_formula]

theorem nativeHeatStep_hInit_067_Gen : nativeHeatInitGen 67 = nativeHeat067Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_067_Gen, nativeHeatStep_hVar_067_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat067Init00_formula
    · exact nativeHeat067Init01_formula
    · exact nativeHeat067Init02_formula
    · exact nativeHeat067Init03_formula
    · exact nativeHeat067Init04_formula
    · exact nativeHeat067Init05_formula
    · exact nativeHeat067Init06_formula
    · exact nativeHeat067Init07_formula
    · exact nativeHeat067Init08_formula
    · exact nativeHeat067Init09_formula
    · exact nativeHeat067Init10_formula
    · exact nativeHeat067Init11_formula
    · exact nativeHeat067Init12_formula
    · exact nativeHeat067Init13_formula
    · exact nativeHeat067Init14_formula
    · exact nativeHeat067Init15_formula
    · exact nativeHeat067Init16_formula
    · exact nativeHeat067Init17_formula
    · exact nativeHeat067Init18_formula
    · exact nativeHeat067Init19_formula
    · exact nativeHeat067Init20_formula
theorem nativeHeatStep_hBase_067_Gen : nativeHeatBaseGen 67 = nativeHeat067Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_067_Gen, nativeHeatStep_hInit_067_Gen, nativeHeat067Base_formula]

theorem nativeHeatStep_hFixed_067_Gen : nativeHeatFixedGen 67 = nativeHeat067Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_067_Gen, nativeHeatStep_hFr_067_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat067Fixed01_formula
    · exact nativeHeat067Fixed02_formula
    · exact nativeHeat067Fixed03_formula
    · exact nativeHeat067Fixed04_formula
    · exact nativeHeat067Fixed05_formula
    · exact nativeHeat067Fixed06_formula
    · exact nativeHeat067Fixed07_formula
    · exact nativeHeat067Fixed08_formula
    · exact nativeHeat067Fixed09_formula
    · exact nativeHeat067Fixed10_formula
    · exact nativeHeat067Fixed11_formula
    · exact nativeHeat067Fixed12_formula
    · exact nativeHeat067Fixed13_formula
    · exact nativeHeat067Fixed14_formula
    · exact nativeHeat067Fixed15_formula
    · exact nativeHeat067Fixed16_formula
    · exact nativeHeat067Fixed17_formula
    · exact nativeHeat067Fixed18_formula
    · exact nativeHeat067Fixed19_formula
    · exact nativeHeat067Fixed20_formula

theorem nativeHeatStep_chk_067_Gen :
    nativeHeatPassRootsOk nativeGap068Old nativeHeat067Frames nativeHeat067Coef nativeHeat067Fixed nativeHeat067Base 48 nativeHeat067Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_067_Gen : NativeHeatStepPassNum 67 := by
  refine nativeHeatStepPassNum_of_literals 67 nativeGap068Old nativeHeat067Frames (nativeHeatExpArg nativeGap068Old)
    nativeHeat067Exp nativeHeat067Coef nativeHeat067Fixed nativeHeat067Init nativeHeat067Base nativeHeatStep_hOld_067_Gen
    nativeHeatStep_hFr_067_Gen nativeHeatStep_hArg_067_Gen nativeHeatStep_hExp_067_Gen
    nativeHeatStep_hCoef_067_Gen nativeHeatStep_hFixed_067_Gen
    nativeHeatStep_hInit_067_Gen nativeHeatStep_hBase_067_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_067_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_067_Gen :
    nativeHeatY0Gen 67 = nativeShiftedFrame 1 (min nativeGap068Old.x nativeGap068Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_067_Gen, nativeHeatStep_hInd_067_Gen]

theorem nativeHeatStepFrameNum_067_Gen : NativeHeatStepFrameNum 67 := by
  have h1 := nativeHeatStep_hOld_067_Gen
  have h2 := nativeHeatStep_hInd_067_Gen
  have h3 := nativeHeatStep_hVar_067_Gen
  have h4 := nativeHeatStep_hQm_067_Gen
  have h5 := nativeHeatStep_hQN_067_Gen
  have h6 := nativeHeatStep_hY0_067_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_067_Gen : NativeHeatStepIndivNum 67 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 67 (by norm_num)) = nativeGap068Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_067_Gen]; exact nativeGap068Old_source
  · rw [hc, nativeHeatStep_hInd_067_Gen]; exact nativeGap068Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_067_Gen : nativeHeatY48Gen 67 = nativeHeat067Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_067_Gen, nativeHeatStep_hFr_067_Gen,
    nativeHeatStep_hCoef_067_Gen, nativeHeatStep_hFixed_067_Gen,
    nativeHeatStep_hBase_067_Gen]
  exact nativeHeat067All48

theorem nativeHeatResultGen_067 : nativeHeatResultGen 67 = nativeHeat067Result := by
  rw [← nativeHeat067Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_067_Gen, nativeHeatStep_hY0_067_Gen, nativeHeatStep_hExp_067_Gen,
    nativeHeatStep_hInit_067_Gen, nativeHeatStep_hFixed_067_Gen]

end ASDExplicitGamma.Native

end
