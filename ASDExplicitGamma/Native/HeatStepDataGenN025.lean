module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat025Complete
public import ASDExplicitGamma.Numerics.Native.Gap026Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_025_Gen : nativeHeatOldRowGen 25 = nativeGap026Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_025_Gen : nativeHeatIndividualGen 25 = nativeGap026Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_025_Gen : nativeHeatGenVariance 25 = nativeHeat025Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_025_Gen, nativeHeat025Variance_formula]

theorem nativeHeatStep_hSpec_025_Gen : nativeHeatGenSpectral 25 = nativeHeat025Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_025_Gen, nativeHeat025Variance_formula]

theorem nativeHeatStep_hQm_025_Gen : nativeHeatGenQm 25 = nativeHeat025Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_025_Gen, nativeHeatStep_hSpec_025_Gen,
    nativeHeat025Qm_formula]

theorem nativeHeatStep_hQN_025_Gen : nativeHeatQNGen 25 = nativeHeat025QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_025_Gen, nativeHeat025QN_formula]

theorem nativeHeatStep_hFr_025_Gen : nativeHeatFramesGen 25 = nativeHeat025Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_025_Gen, nativeHeatStep_hInd_025_Gen,
    nativeHeatStep_hVar_025_Gen, nativeHeatStep_hQN_025_Gen, nativeHeat025Frames_formula]

theorem nativeHeatStep_hArg_025_Gen : nativeHeatExpArgGen 25 = nativeHeatExpArg nativeGap026Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_025_Gen]

theorem nativeHeatStep_hExp_025_Gen : nativeHeatExpGen 25 = nativeHeat025Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_025_Gen, nativeHeat025Exp_formula]

theorem nativeHeatStep_hCoef_025_Gen : nativeHeatCoefGen 25 = nativeHeat025Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_025_Gen, nativeHeat025Coef_formula]

theorem nativeHeatStep_hInit_025_Gen : nativeHeatInitGen 25 = nativeHeat025Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_025_Gen, nativeHeatStep_hVar_025_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat025Init00_formula
    · exact nativeHeat025Init01_formula
    · exact nativeHeat025Init02_formula
    · exact nativeHeat025Init03_formula
    · exact nativeHeat025Init04_formula
    · exact nativeHeat025Init05_formula
    · exact nativeHeat025Init06_formula
    · exact nativeHeat025Init07_formula
    · exact nativeHeat025Init08_formula
    · exact nativeHeat025Init09_formula
    · exact nativeHeat025Init10_formula
    · exact nativeHeat025Init11_formula
    · exact nativeHeat025Init12_formula
    · exact nativeHeat025Init13_formula
    · exact nativeHeat025Init14_formula
    · exact nativeHeat025Init15_formula
    · exact nativeHeat025Init16_formula
    · exact nativeHeat025Init17_formula
    · exact nativeHeat025Init18_formula
    · exact nativeHeat025Init19_formula
    · exact nativeHeat025Init20_formula
theorem nativeHeatStep_hBase_025_Gen : nativeHeatBaseGen 25 = nativeHeat025Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_025_Gen, nativeHeatStep_hInit_025_Gen, nativeHeat025Base_formula]

theorem nativeHeatStep_hFixed_025_Gen : nativeHeatFixedGen 25 = nativeHeat025Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_025_Gen, nativeHeatStep_hFr_025_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat025Fixed01_formula
    · exact nativeHeat025Fixed02_formula
    · exact nativeHeat025Fixed03_formula
    · exact nativeHeat025Fixed04_formula
    · exact nativeHeat025Fixed05_formula
    · exact nativeHeat025Fixed06_formula
    · exact nativeHeat025Fixed07_formula
    · exact nativeHeat025Fixed08_formula
    · exact nativeHeat025Fixed09_formula
    · exact nativeHeat025Fixed10_formula
    · exact nativeHeat025Fixed11_formula
    · exact nativeHeat025Fixed12_formula
    · exact nativeHeat025Fixed13_formula
    · exact nativeHeat025Fixed14_formula
    · exact nativeHeat025Fixed15_formula
    · exact nativeHeat025Fixed16_formula
    · exact nativeHeat025Fixed17_formula
    · exact nativeHeat025Fixed18_formula
    · exact nativeHeat025Fixed19_formula
    · exact nativeHeat025Fixed20_formula

theorem nativeHeatStep_chk_025_Gen :
    nativeHeatPassRootsOk nativeGap026Old nativeHeat025Frames nativeHeat025Coef nativeHeat025Fixed nativeHeat025Base 48 nativeHeat025Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_025_Gen : NativeHeatStepPassNum 25 := by
  refine nativeHeatStepPassNum_of_literals 25 nativeGap026Old nativeHeat025Frames (nativeHeatExpArg nativeGap026Old)
    nativeHeat025Exp nativeHeat025Coef nativeHeat025Fixed nativeHeat025Init nativeHeat025Base nativeHeatStep_hOld_025_Gen
    nativeHeatStep_hFr_025_Gen nativeHeatStep_hArg_025_Gen nativeHeatStep_hExp_025_Gen
    nativeHeatStep_hCoef_025_Gen nativeHeatStep_hFixed_025_Gen
    nativeHeatStep_hInit_025_Gen nativeHeatStep_hBase_025_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_025_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_025_Gen :
    nativeHeatY0Gen 25 = nativeShiftedFrame 1 (min nativeGap026Old.x nativeGap026Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_025_Gen, nativeHeatStep_hInd_025_Gen]

theorem nativeHeatStepFrameNum_025_Gen : NativeHeatStepFrameNum 25 := by
  have h1 := nativeHeatStep_hOld_025_Gen
  have h2 := nativeHeatStep_hInd_025_Gen
  have h3 := nativeHeatStep_hVar_025_Gen
  have h4 := nativeHeatStep_hQm_025_Gen
  have h5 := nativeHeatStep_hQN_025_Gen
  have h6 := nativeHeatStep_hY0_025_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_025_Gen : NativeHeatStepIndivNum 25 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 25 (by norm_num)) = nativeGap026Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_025_Gen]; exact nativeGap026Old_source
  · rw [hc, nativeHeatStep_hInd_025_Gen]; exact nativeGap026Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_025_Gen : nativeHeatY48Gen 25 = nativeHeat025Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_025_Gen, nativeHeatStep_hFr_025_Gen,
    nativeHeatStep_hCoef_025_Gen, nativeHeatStep_hFixed_025_Gen,
    nativeHeatStep_hBase_025_Gen]
  exact nativeHeat025All48

theorem nativeHeatResultGen_025 : nativeHeatResultGen 25 = nativeHeat025Result := by
  rw [← nativeHeat025Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_025_Gen, nativeHeatStep_hY0_025_Gen, nativeHeatStep_hExp_025_Gen,
    nativeHeatStep_hInit_025_Gen, nativeHeatStep_hFixed_025_Gen]

end ASDExplicitGamma.Native

end
