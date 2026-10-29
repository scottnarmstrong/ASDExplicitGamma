module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat063Complete
public import ASDExplicitGamma.Numerics.Native.Gap064Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_063_Gen : nativeHeatOldRowGen 63 = nativeGap064Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_063_Gen : nativeHeatIndividualGen 63 = nativeGap064Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_063_Gen : nativeHeatGenVariance 63 = nativeHeat063Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_063_Gen, nativeHeat063Variance_formula]

theorem nativeHeatStep_hSpec_063_Gen : nativeHeatGenSpectral 63 = nativeHeat063Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_063_Gen, nativeHeat063Variance_formula]

theorem nativeHeatStep_hQm_063_Gen : nativeHeatGenQm 63 = nativeHeat063Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_063_Gen, nativeHeatStep_hSpec_063_Gen,
    nativeHeat063Qm_formula]

theorem nativeHeatStep_hQN_063_Gen : nativeHeatQNGen 63 = nativeHeat063QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_063_Gen, nativeHeat063QN_formula]

theorem nativeHeatStep_hFr_063_Gen : nativeHeatFramesGen 63 = nativeHeat063Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_063_Gen, nativeHeatStep_hInd_063_Gen,
    nativeHeatStep_hVar_063_Gen, nativeHeatStep_hQN_063_Gen, nativeHeat063Frames_formula]

theorem nativeHeatStep_hArg_063_Gen : nativeHeatExpArgGen 63 = nativeHeatExpArg nativeGap064Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_063_Gen]

theorem nativeHeatStep_hExp_063_Gen : nativeHeatExpGen 63 = nativeHeat063Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_063_Gen, nativeHeat063Exp_formula]

theorem nativeHeatStep_hCoef_063_Gen : nativeHeatCoefGen 63 = nativeHeat063Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_063_Gen, nativeHeat063Coef_formula]

theorem nativeHeatStep_hInit_063_Gen : nativeHeatInitGen 63 = nativeHeat063Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_063_Gen, nativeHeatStep_hVar_063_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat063Init00_formula
    · exact nativeHeat063Init01_formula
    · exact nativeHeat063Init02_formula
    · exact nativeHeat063Init03_formula
    · exact nativeHeat063Init04_formula
    · exact nativeHeat063Init05_formula
    · exact nativeHeat063Init06_formula
    · exact nativeHeat063Init07_formula
    · exact nativeHeat063Init08_formula
    · exact nativeHeat063Init09_formula
    · exact nativeHeat063Init10_formula
    · exact nativeHeat063Init11_formula
    · exact nativeHeat063Init12_formula
    · exact nativeHeat063Init13_formula
    · exact nativeHeat063Init14_formula
    · exact nativeHeat063Init15_formula
    · exact nativeHeat063Init16_formula
    · exact nativeHeat063Init17_formula
    · exact nativeHeat063Init18_formula
    · exact nativeHeat063Init19_formula
    · exact nativeHeat063Init20_formula
theorem nativeHeatStep_hBase_063_Gen : nativeHeatBaseGen 63 = nativeHeat063Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_063_Gen, nativeHeatStep_hInit_063_Gen, nativeHeat063Base_formula]

theorem nativeHeatStep_hFixed_063_Gen : nativeHeatFixedGen 63 = nativeHeat063Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_063_Gen, nativeHeatStep_hFr_063_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat063Fixed01_formula
    · exact nativeHeat063Fixed02_formula
    · exact nativeHeat063Fixed03_formula
    · exact nativeHeat063Fixed04_formula
    · exact nativeHeat063Fixed05_formula
    · exact nativeHeat063Fixed06_formula
    · exact nativeHeat063Fixed07_formula
    · exact nativeHeat063Fixed08_formula
    · exact nativeHeat063Fixed09_formula
    · exact nativeHeat063Fixed10_formula
    · exact nativeHeat063Fixed11_formula
    · exact nativeHeat063Fixed12_formula
    · exact nativeHeat063Fixed13_formula
    · exact nativeHeat063Fixed14_formula
    · exact nativeHeat063Fixed15_formula
    · exact nativeHeat063Fixed16_formula
    · exact nativeHeat063Fixed17_formula
    · exact nativeHeat063Fixed18_formula
    · exact nativeHeat063Fixed19_formula
    · exact nativeHeat063Fixed20_formula

theorem nativeHeatStep_chk_063_Gen :
    nativeHeatPassRootsOk nativeGap064Old nativeHeat063Frames nativeHeat063Coef nativeHeat063Fixed nativeHeat063Base 48 nativeHeat063Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_063_Gen : NativeHeatStepPassNum 63 := by
  refine nativeHeatStepPassNum_of_literals 63 nativeGap064Old nativeHeat063Frames (nativeHeatExpArg nativeGap064Old)
    nativeHeat063Exp nativeHeat063Coef nativeHeat063Fixed nativeHeat063Init nativeHeat063Base nativeHeatStep_hOld_063_Gen
    nativeHeatStep_hFr_063_Gen nativeHeatStep_hArg_063_Gen nativeHeatStep_hExp_063_Gen
    nativeHeatStep_hCoef_063_Gen nativeHeatStep_hFixed_063_Gen
    nativeHeatStep_hInit_063_Gen nativeHeatStep_hBase_063_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_063_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_063_Gen :
    nativeHeatY0Gen 63 = nativeShiftedFrame 1 (min nativeGap064Old.x nativeGap064Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_063_Gen, nativeHeatStep_hInd_063_Gen]

theorem nativeHeatStepFrameNum_063_Gen : NativeHeatStepFrameNum 63 := by
  have h1 := nativeHeatStep_hOld_063_Gen
  have h2 := nativeHeatStep_hInd_063_Gen
  have h3 := nativeHeatStep_hVar_063_Gen
  have h4 := nativeHeatStep_hQm_063_Gen
  have h5 := nativeHeatStep_hQN_063_Gen
  have h6 := nativeHeatStep_hY0_063_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_063_Gen : NativeHeatStepIndivNum 63 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 63 (by norm_num)) = nativeGap064Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_063_Gen]; exact nativeGap064Old_source
  · rw [hc, nativeHeatStep_hInd_063_Gen]; exact nativeGap064Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_063_Gen : nativeHeatY48Gen 63 = nativeHeat063Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_063_Gen, nativeHeatStep_hFr_063_Gen,
    nativeHeatStep_hCoef_063_Gen, nativeHeatStep_hFixed_063_Gen,
    nativeHeatStep_hBase_063_Gen]
  exact nativeHeat063All48

theorem nativeHeatResultGen_063 : nativeHeatResultGen 63 = nativeHeat063Result := by
  rw [← nativeHeat063Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_063_Gen, nativeHeatStep_hY0_063_Gen, nativeHeatStep_hExp_063_Gen,
    nativeHeatStep_hInit_063_Gen, nativeHeatStep_hFixed_063_Gen]

end ASDExplicitGamma.Native

end
