module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat050Complete
public import ASDExplicitGamma.Numerics.Native.Gap051Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_050_Gen : nativeHeatOldRowGen 50 = nativeGap051Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_050_Gen : nativeHeatIndividualGen 50 = nativeGap051Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_050_Gen : nativeHeatGenVariance 50 = nativeHeat050Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_050_Gen, nativeHeat050Variance_formula]

theorem nativeHeatStep_hSpec_050_Gen : nativeHeatGenSpectral 50 = nativeHeat050Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_050_Gen, nativeHeat050Variance_formula]

theorem nativeHeatStep_hQm_050_Gen : nativeHeatGenQm 50 = nativeHeat050Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_050_Gen, nativeHeatStep_hSpec_050_Gen,
    nativeHeat050Qm_formula]

theorem nativeHeatStep_hQN_050_Gen : nativeHeatQNGen 50 = nativeHeat050QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_050_Gen, nativeHeat050QN_formula]

theorem nativeHeatStep_hFr_050_Gen : nativeHeatFramesGen 50 = nativeHeat050Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_050_Gen, nativeHeatStep_hInd_050_Gen,
    nativeHeatStep_hVar_050_Gen, nativeHeatStep_hQN_050_Gen, nativeHeat050Frames_formula]

theorem nativeHeatStep_hArg_050_Gen : nativeHeatExpArgGen 50 = nativeHeatExpArg nativeGap051Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_050_Gen]

theorem nativeHeatStep_hExp_050_Gen : nativeHeatExpGen 50 = nativeHeat050Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_050_Gen, nativeHeat050Exp_formula]

theorem nativeHeatStep_hCoef_050_Gen : nativeHeatCoefGen 50 = nativeHeat050Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_050_Gen, nativeHeat050Coef_formula]

theorem nativeHeatStep_hInit_050_Gen : nativeHeatInitGen 50 = nativeHeat050Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_050_Gen, nativeHeatStep_hVar_050_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat050Init00_formula
    · exact nativeHeat050Init01_formula
    · exact nativeHeat050Init02_formula
    · exact nativeHeat050Init03_formula
    · exact nativeHeat050Init04_formula
    · exact nativeHeat050Init05_formula
    · exact nativeHeat050Init06_formula
    · exact nativeHeat050Init07_formula
    · exact nativeHeat050Init08_formula
    · exact nativeHeat050Init09_formula
    · exact nativeHeat050Init10_formula
    · exact nativeHeat050Init11_formula
    · exact nativeHeat050Init12_formula
    · exact nativeHeat050Init13_formula
    · exact nativeHeat050Init14_formula
    · exact nativeHeat050Init15_formula
    · exact nativeHeat050Init16_formula
    · exact nativeHeat050Init17_formula
    · exact nativeHeat050Init18_formula
    · exact nativeHeat050Init19_formula
    · exact nativeHeat050Init20_formula
theorem nativeHeatStep_hBase_050_Gen : nativeHeatBaseGen 50 = nativeHeat050Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_050_Gen, nativeHeatStep_hInit_050_Gen, nativeHeat050Base_formula]

theorem nativeHeatStep_hFixed_050_Gen : nativeHeatFixedGen 50 = nativeHeat050Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_050_Gen, nativeHeatStep_hFr_050_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat050Fixed01_formula
    · exact nativeHeat050Fixed02_formula
    · exact nativeHeat050Fixed03_formula
    · exact nativeHeat050Fixed04_formula
    · exact nativeHeat050Fixed05_formula
    · exact nativeHeat050Fixed06_formula
    · exact nativeHeat050Fixed07_formula
    · exact nativeHeat050Fixed08_formula
    · exact nativeHeat050Fixed09_formula
    · exact nativeHeat050Fixed10_formula
    · exact nativeHeat050Fixed11_formula
    · exact nativeHeat050Fixed12_formula
    · exact nativeHeat050Fixed13_formula
    · exact nativeHeat050Fixed14_formula
    · exact nativeHeat050Fixed15_formula
    · exact nativeHeat050Fixed16_formula
    · exact nativeHeat050Fixed17_formula
    · exact nativeHeat050Fixed18_formula
    · exact nativeHeat050Fixed19_formula
    · exact nativeHeat050Fixed20_formula

theorem nativeHeatStep_chk_050_Gen :
    nativeHeatPassRootsOk nativeGap051Old nativeHeat050Frames nativeHeat050Coef nativeHeat050Fixed nativeHeat050Base 48 nativeHeat050Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_050_Gen : NativeHeatStepPassNum 50 := by
  refine nativeHeatStepPassNum_of_literals 50 nativeGap051Old nativeHeat050Frames (nativeHeatExpArg nativeGap051Old)
    nativeHeat050Exp nativeHeat050Coef nativeHeat050Fixed nativeHeat050Init nativeHeat050Base nativeHeatStep_hOld_050_Gen
    nativeHeatStep_hFr_050_Gen nativeHeatStep_hArg_050_Gen nativeHeatStep_hExp_050_Gen
    nativeHeatStep_hCoef_050_Gen nativeHeatStep_hFixed_050_Gen
    nativeHeatStep_hInit_050_Gen nativeHeatStep_hBase_050_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_050_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_050_Gen :
    nativeHeatY0Gen 50 = nativeShiftedFrame 1 (min nativeGap051Old.x nativeGap051Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_050_Gen, nativeHeatStep_hInd_050_Gen]

theorem nativeHeatStepFrameNum_050_Gen : NativeHeatStepFrameNum 50 := by
  have h1 := nativeHeatStep_hOld_050_Gen
  have h2 := nativeHeatStep_hInd_050_Gen
  have h3 := nativeHeatStep_hVar_050_Gen
  have h4 := nativeHeatStep_hQm_050_Gen
  have h5 := nativeHeatStep_hQN_050_Gen
  have h6 := nativeHeatStep_hY0_050_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_050_Gen : NativeHeatStepIndivNum 50 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 50 (by norm_num)) = nativeGap051Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_050_Gen]; exact nativeGap051Old_source
  · rw [hc, nativeHeatStep_hInd_050_Gen]; exact nativeGap051Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_050_Gen : nativeHeatY48Gen 50 = nativeHeat050Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_050_Gen, nativeHeatStep_hFr_050_Gen,
    nativeHeatStep_hCoef_050_Gen, nativeHeatStep_hFixed_050_Gen,
    nativeHeatStep_hBase_050_Gen]
  exact nativeHeat050All48

theorem nativeHeatResultGen_050 : nativeHeatResultGen 50 = nativeHeat050Result := by
  rw [← nativeHeat050Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_050_Gen, nativeHeatStep_hY0_050_Gen, nativeHeatStep_hExp_050_Gen,
    nativeHeatStep_hInit_050_Gen, nativeHeatStep_hFixed_050_Gen]

end ASDExplicitGamma.Native

end
