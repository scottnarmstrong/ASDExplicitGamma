module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat118Complete
public import ASDExplicitGamma.Numerics.Native.Gap119Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_118_Gen : nativeHeatOldRowGen 118 = nativeGap119Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_118_Gen : nativeHeatIndividualGen 118 = nativeGap119Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_118_Gen : nativeHeatGenVariance 118 = nativeHeat118Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_118_Gen, nativeHeat118Variance_formula]

theorem nativeHeatStep_hSpec_118_Gen : nativeHeatGenSpectral 118 = nativeHeat118Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_118_Gen, nativeHeat118Variance_formula]

theorem nativeHeatStep_hQm_118_Gen : nativeHeatGenQm 118 = nativeHeat118Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_118_Gen, nativeHeatStep_hSpec_118_Gen,
    nativeHeat118Qm_formula]

theorem nativeHeatStep_hQN_118_Gen : nativeHeatQNGen 118 = nativeHeat118QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_118_Gen, nativeHeat118QN_formula]

theorem nativeHeatStep_hFr_118_Gen : nativeHeatFramesGen 118 = nativeHeat118Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_118_Gen, nativeHeatStep_hInd_118_Gen,
    nativeHeatStep_hVar_118_Gen, nativeHeatStep_hQN_118_Gen, nativeHeat118Frames_formula]

theorem nativeHeatStep_hArg_118_Gen : nativeHeatExpArgGen 118 = nativeHeatExpArg nativeGap119Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_118_Gen]

theorem nativeHeatStep_hExp_118_Gen : nativeHeatExpGen 118 = nativeHeat118Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_118_Gen, nativeHeat118Exp_formula]

theorem nativeHeatStep_hCoef_118_Gen : nativeHeatCoefGen 118 = nativeHeat118Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_118_Gen, nativeHeat118Coef_formula]

theorem nativeHeatStep_hInit_118_Gen : nativeHeatInitGen 118 = nativeHeat118Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_118_Gen, nativeHeatStep_hVar_118_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat118Init00_formula
    · exact nativeHeat118Init01_formula
    · exact nativeHeat118Init02_formula
    · exact nativeHeat118Init03_formula
    · exact nativeHeat118Init04_formula
    · exact nativeHeat118Init05_formula
    · exact nativeHeat118Init06_formula
    · exact nativeHeat118Init07_formula
    · exact nativeHeat118Init08_formula
    · exact nativeHeat118Init09_formula
    · exact nativeHeat118Init10_formula
    · exact nativeHeat118Init11_formula
    · exact nativeHeat118Init12_formula
    · exact nativeHeat118Init13_formula
    · exact nativeHeat118Init14_formula
    · exact nativeHeat118Init15_formula
    · exact nativeHeat118Init16_formula
    · exact nativeHeat118Init17_formula
    · exact nativeHeat118Init18_formula
    · exact nativeHeat118Init19_formula
    · exact nativeHeat118Init20_formula
theorem nativeHeatStep_hBase_118_Gen : nativeHeatBaseGen 118 = nativeHeat118Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_118_Gen, nativeHeatStep_hInit_118_Gen, nativeHeat118Base_formula]

theorem nativeHeatStep_hFixed_118_Gen : nativeHeatFixedGen 118 = nativeHeat118Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_118_Gen, nativeHeatStep_hFr_118_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat118Fixed01_formula
    · exact nativeHeat118Fixed02_formula
    · exact nativeHeat118Fixed03_formula
    · exact nativeHeat118Fixed04_formula
    · exact nativeHeat118Fixed05_formula
    · exact nativeHeat118Fixed06_formula
    · exact nativeHeat118Fixed07_formula
    · exact nativeHeat118Fixed08_formula
    · exact nativeHeat118Fixed09_formula
    · exact nativeHeat118Fixed10_formula
    · exact nativeHeat118Fixed11_formula
    · exact nativeHeat118Fixed12_formula
    · exact nativeHeat118Fixed13_formula
    · exact nativeHeat118Fixed14_formula
    · exact nativeHeat118Fixed15_formula
    · exact nativeHeat118Fixed16_formula
    · exact nativeHeat118Fixed17_formula
    · exact nativeHeat118Fixed18_formula
    · exact nativeHeat118Fixed19_formula
    · exact nativeHeat118Fixed20_formula

theorem nativeHeatStep_chk_118_Gen :
    nativeHeatPassRootsOk nativeGap119Old nativeHeat118Frames nativeHeat118Coef nativeHeat118Fixed nativeHeat118Base 48 nativeHeat118Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_118_Gen : NativeHeatStepPassNum 118 := by
  refine nativeHeatStepPassNum_of_literals 118 nativeGap119Old nativeHeat118Frames (nativeHeatExpArg nativeGap119Old)
    nativeHeat118Exp nativeHeat118Coef nativeHeat118Fixed nativeHeat118Init nativeHeat118Base nativeHeatStep_hOld_118_Gen
    nativeHeatStep_hFr_118_Gen nativeHeatStep_hArg_118_Gen nativeHeatStep_hExp_118_Gen
    nativeHeatStep_hCoef_118_Gen nativeHeatStep_hFixed_118_Gen
    nativeHeatStep_hInit_118_Gen nativeHeatStep_hBase_118_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_118_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_118_Gen :
    nativeHeatY0Gen 118 = nativeShiftedFrame 1 (min nativeGap119Old.x nativeGap119Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_118_Gen, nativeHeatStep_hInd_118_Gen]

theorem nativeHeatStepFrameNum_118_Gen : NativeHeatStepFrameNum 118 := by
  have h1 := nativeHeatStep_hOld_118_Gen
  have h2 := nativeHeatStep_hInd_118_Gen
  have h3 := nativeHeatStep_hVar_118_Gen
  have h4 := nativeHeatStep_hQm_118_Gen
  have h5 := nativeHeatStep_hQN_118_Gen
  have h6 := nativeHeatStep_hY0_118_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_118_Gen : NativeHeatStepIndivNum 118 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 118 (by norm_num)) = nativeGap119Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_118_Gen]; exact nativeGap119Old_source
  · rw [hc, nativeHeatStep_hInd_118_Gen]; exact nativeGap119Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_118_Gen : nativeHeatY48Gen 118 = nativeHeat118Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_118_Gen, nativeHeatStep_hFr_118_Gen,
    nativeHeatStep_hCoef_118_Gen, nativeHeatStep_hFixed_118_Gen,
    nativeHeatStep_hBase_118_Gen]
  exact nativeHeat118All48

theorem nativeHeatResultGen_118 : nativeHeatResultGen 118 = nativeHeat118Result := by
  rw [← nativeHeat118Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_118_Gen, nativeHeatStep_hY0_118_Gen, nativeHeatStep_hExp_118_Gen,
    nativeHeatStep_hInit_118_Gen, nativeHeatStep_hFixed_118_Gen]

end ASDExplicitGamma.Native

end
