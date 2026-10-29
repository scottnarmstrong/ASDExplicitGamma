module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat023Complete
public import ASDExplicitGamma.Numerics.Native.Gap024Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_023_Gen : nativeHeatOldRowGen 23 = nativeGap024Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_023_Gen : nativeHeatIndividualGen 23 = nativeGap024Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_023_Gen : nativeHeatGenVariance 23 = nativeHeat023Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_023_Gen, nativeHeat023Variance_formula]

theorem nativeHeatStep_hSpec_023_Gen : nativeHeatGenSpectral 23 = nativeHeat023Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_023_Gen, nativeHeat023Variance_formula]

theorem nativeHeatStep_hQm_023_Gen : nativeHeatGenQm 23 = nativeHeat023Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_023_Gen, nativeHeatStep_hSpec_023_Gen,
    nativeHeat023Qm_formula]

theorem nativeHeatStep_hQN_023_Gen : nativeHeatQNGen 23 = nativeHeat023QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_023_Gen, nativeHeat023QN_formula]

theorem nativeHeatStep_hFr_023_Gen : nativeHeatFramesGen 23 = nativeHeat023Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_023_Gen, nativeHeatStep_hInd_023_Gen,
    nativeHeatStep_hVar_023_Gen, nativeHeatStep_hQN_023_Gen, nativeHeat023Frames_formula]

theorem nativeHeatStep_hArg_023_Gen : nativeHeatExpArgGen 23 = nativeHeatExpArg nativeGap024Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_023_Gen]

theorem nativeHeatStep_hExp_023_Gen : nativeHeatExpGen 23 = nativeHeat023Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_023_Gen, nativeHeat023Exp_formula]

theorem nativeHeatStep_hCoef_023_Gen : nativeHeatCoefGen 23 = nativeHeat023Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_023_Gen, nativeHeat023Coef_formula]

theorem nativeHeatStep_hInit_023_Gen : nativeHeatInitGen 23 = nativeHeat023Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_023_Gen, nativeHeatStep_hVar_023_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat023Init00_formula
    · exact nativeHeat023Init01_formula
    · exact nativeHeat023Init02_formula
    · exact nativeHeat023Init03_formula
    · exact nativeHeat023Init04_formula
    · exact nativeHeat023Init05_formula
    · exact nativeHeat023Init06_formula
    · exact nativeHeat023Init07_formula
    · exact nativeHeat023Init08_formula
    · exact nativeHeat023Init09_formula
    · exact nativeHeat023Init10_formula
    · exact nativeHeat023Init11_formula
    · exact nativeHeat023Init12_formula
    · exact nativeHeat023Init13_formula
    · exact nativeHeat023Init14_formula
    · exact nativeHeat023Init15_formula
    · exact nativeHeat023Init16_formula
    · exact nativeHeat023Init17_formula
    · exact nativeHeat023Init18_formula
    · exact nativeHeat023Init19_formula
    · exact nativeHeat023Init20_formula
theorem nativeHeatStep_hBase_023_Gen : nativeHeatBaseGen 23 = nativeHeat023Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_023_Gen, nativeHeatStep_hInit_023_Gen, nativeHeat023Base_formula]

theorem nativeHeatStep_hFixed_023_Gen : nativeHeatFixedGen 23 = nativeHeat023Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_023_Gen, nativeHeatStep_hFr_023_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat023Fixed01_formula
    · exact nativeHeat023Fixed02_formula
    · exact nativeHeat023Fixed03_formula
    · exact nativeHeat023Fixed04_formula
    · exact nativeHeat023Fixed05_formula
    · exact nativeHeat023Fixed06_formula
    · exact nativeHeat023Fixed07_formula
    · exact nativeHeat023Fixed08_formula
    · exact nativeHeat023Fixed09_formula
    · exact nativeHeat023Fixed10_formula
    · exact nativeHeat023Fixed11_formula
    · exact nativeHeat023Fixed12_formula
    · exact nativeHeat023Fixed13_formula
    · exact nativeHeat023Fixed14_formula
    · exact nativeHeat023Fixed15_formula
    · exact nativeHeat023Fixed16_formula
    · exact nativeHeat023Fixed17_formula
    · exact nativeHeat023Fixed18_formula
    · exact nativeHeat023Fixed19_formula
    · exact nativeHeat023Fixed20_formula

theorem nativeHeatStep_chk_023_Gen :
    nativeHeatPassRootsOk nativeGap024Old nativeHeat023Frames nativeHeat023Coef nativeHeat023Fixed nativeHeat023Base 48 nativeHeat023Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_023_Gen : NativeHeatStepPassNum 23 := by
  refine nativeHeatStepPassNum_of_literals 23 nativeGap024Old nativeHeat023Frames (nativeHeatExpArg nativeGap024Old)
    nativeHeat023Exp nativeHeat023Coef nativeHeat023Fixed nativeHeat023Init nativeHeat023Base nativeHeatStep_hOld_023_Gen
    nativeHeatStep_hFr_023_Gen nativeHeatStep_hArg_023_Gen nativeHeatStep_hExp_023_Gen
    nativeHeatStep_hCoef_023_Gen nativeHeatStep_hFixed_023_Gen
    nativeHeatStep_hInit_023_Gen nativeHeatStep_hBase_023_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_023_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_023_Gen :
    nativeHeatY0Gen 23 = nativeShiftedFrame 1 (min nativeGap024Old.x nativeGap024Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_023_Gen, nativeHeatStep_hInd_023_Gen]

theorem nativeHeatStepFrameNum_023_Gen : NativeHeatStepFrameNum 23 := by
  have h1 := nativeHeatStep_hOld_023_Gen
  have h2 := nativeHeatStep_hInd_023_Gen
  have h3 := nativeHeatStep_hVar_023_Gen
  have h4 := nativeHeatStep_hQm_023_Gen
  have h5 := nativeHeatStep_hQN_023_Gen
  have h6 := nativeHeatStep_hY0_023_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_023_Gen : NativeHeatStepIndivNum 23 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 23 (by norm_num)) = nativeGap024Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_023_Gen]; exact nativeGap024Old_source
  · rw [hc, nativeHeatStep_hInd_023_Gen]; exact nativeGap024Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_023_Gen : nativeHeatY48Gen 23 = nativeHeat023Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_023_Gen, nativeHeatStep_hFr_023_Gen,
    nativeHeatStep_hCoef_023_Gen, nativeHeatStep_hFixed_023_Gen,
    nativeHeatStep_hBase_023_Gen]
  exact nativeHeat023All48

theorem nativeHeatResultGen_023 : nativeHeatResultGen 23 = nativeHeat023Result := by
  rw [← nativeHeat023Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_023_Gen, nativeHeatStep_hY0_023_Gen, nativeHeatStep_hExp_023_Gen,
    nativeHeatStep_hInit_023_Gen, nativeHeatStep_hFixed_023_Gen]

end ASDExplicitGamma.Native

end
