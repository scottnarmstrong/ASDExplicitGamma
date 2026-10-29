module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat040Complete
public import ASDExplicitGamma.Numerics.Native.Gap041Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_040_Gen : nativeHeatOldRowGen 40 = nativeGap041Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_040_Gen : nativeHeatIndividualGen 40 = nativeGap041Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_040_Gen : nativeHeatGenVariance 40 = nativeHeat040Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_040_Gen, nativeHeat040Variance_formula]

theorem nativeHeatStep_hSpec_040_Gen : nativeHeatGenSpectral 40 = nativeHeat040Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_040_Gen, nativeHeat040Variance_formula]

theorem nativeHeatStep_hQm_040_Gen : nativeHeatGenQm 40 = nativeHeat040Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_040_Gen, nativeHeatStep_hSpec_040_Gen,
    nativeHeat040Qm_formula]

theorem nativeHeatStep_hQN_040_Gen : nativeHeatQNGen 40 = nativeHeat040QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_040_Gen, nativeHeat040QN_formula]

theorem nativeHeatStep_hFr_040_Gen : nativeHeatFramesGen 40 = nativeHeat040Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_040_Gen, nativeHeatStep_hInd_040_Gen,
    nativeHeatStep_hVar_040_Gen, nativeHeatStep_hQN_040_Gen, nativeHeat040Frames_formula]

theorem nativeHeatStep_hArg_040_Gen : nativeHeatExpArgGen 40 = nativeHeatExpArg nativeGap041Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_040_Gen]

theorem nativeHeatStep_hExp_040_Gen : nativeHeatExpGen 40 = nativeHeat040Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_040_Gen, nativeHeat040Exp_formula]

theorem nativeHeatStep_hCoef_040_Gen : nativeHeatCoefGen 40 = nativeHeat040Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_040_Gen, nativeHeat040Coef_formula]

theorem nativeHeatStep_hInit_040_Gen : nativeHeatInitGen 40 = nativeHeat040Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_040_Gen, nativeHeatStep_hVar_040_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat040Init00_formula
    · exact nativeHeat040Init01_formula
    · exact nativeHeat040Init02_formula
    · exact nativeHeat040Init03_formula
    · exact nativeHeat040Init04_formula
    · exact nativeHeat040Init05_formula
    · exact nativeHeat040Init06_formula
    · exact nativeHeat040Init07_formula
    · exact nativeHeat040Init08_formula
    · exact nativeHeat040Init09_formula
    · exact nativeHeat040Init10_formula
    · exact nativeHeat040Init11_formula
    · exact nativeHeat040Init12_formula
    · exact nativeHeat040Init13_formula
    · exact nativeHeat040Init14_formula
    · exact nativeHeat040Init15_formula
    · exact nativeHeat040Init16_formula
    · exact nativeHeat040Init17_formula
    · exact nativeHeat040Init18_formula
    · exact nativeHeat040Init19_formula
    · exact nativeHeat040Init20_formula
theorem nativeHeatStep_hBase_040_Gen : nativeHeatBaseGen 40 = nativeHeat040Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_040_Gen, nativeHeatStep_hInit_040_Gen, nativeHeat040Base_formula]

theorem nativeHeatStep_hFixed_040_Gen : nativeHeatFixedGen 40 = nativeHeat040Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_040_Gen, nativeHeatStep_hFr_040_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat040Fixed01_formula
    · exact nativeHeat040Fixed02_formula
    · exact nativeHeat040Fixed03_formula
    · exact nativeHeat040Fixed04_formula
    · exact nativeHeat040Fixed05_formula
    · exact nativeHeat040Fixed06_formula
    · exact nativeHeat040Fixed07_formula
    · exact nativeHeat040Fixed08_formula
    · exact nativeHeat040Fixed09_formula
    · exact nativeHeat040Fixed10_formula
    · exact nativeHeat040Fixed11_formula
    · exact nativeHeat040Fixed12_formula
    · exact nativeHeat040Fixed13_formula
    · exact nativeHeat040Fixed14_formula
    · exact nativeHeat040Fixed15_formula
    · exact nativeHeat040Fixed16_formula
    · exact nativeHeat040Fixed17_formula
    · exact nativeHeat040Fixed18_formula
    · exact nativeHeat040Fixed19_formula
    · exact nativeHeat040Fixed20_formula

theorem nativeHeatStep_chk_040_Gen :
    nativeHeatPassRootsOk nativeGap041Old nativeHeat040Frames nativeHeat040Coef nativeHeat040Fixed nativeHeat040Base 48 nativeHeat040Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_040_Gen : NativeHeatStepPassNum 40 := by
  refine nativeHeatStepPassNum_of_literals 40 nativeGap041Old nativeHeat040Frames (nativeHeatExpArg nativeGap041Old)
    nativeHeat040Exp nativeHeat040Coef nativeHeat040Fixed nativeHeat040Init nativeHeat040Base nativeHeatStep_hOld_040_Gen
    nativeHeatStep_hFr_040_Gen nativeHeatStep_hArg_040_Gen nativeHeatStep_hExp_040_Gen
    nativeHeatStep_hCoef_040_Gen nativeHeatStep_hFixed_040_Gen
    nativeHeatStep_hInit_040_Gen nativeHeatStep_hBase_040_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_040_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_040_Gen :
    nativeHeatY0Gen 40 = nativeShiftedFrame 1 (min nativeGap041Old.x nativeGap041Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_040_Gen, nativeHeatStep_hInd_040_Gen]

theorem nativeHeatStepFrameNum_040_Gen : NativeHeatStepFrameNum 40 := by
  have h1 := nativeHeatStep_hOld_040_Gen
  have h2 := nativeHeatStep_hInd_040_Gen
  have h3 := nativeHeatStep_hVar_040_Gen
  have h4 := nativeHeatStep_hQm_040_Gen
  have h5 := nativeHeatStep_hQN_040_Gen
  have h6 := nativeHeatStep_hY0_040_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_040_Gen : NativeHeatStepIndivNum 40 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 40 (by norm_num)) = nativeGap041Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_040_Gen]; exact nativeGap041Old_source
  · rw [hc, nativeHeatStep_hInd_040_Gen]; exact nativeGap041Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_040_Gen : nativeHeatY48Gen 40 = nativeHeat040Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_040_Gen, nativeHeatStep_hFr_040_Gen,
    nativeHeatStep_hCoef_040_Gen, nativeHeatStep_hFixed_040_Gen,
    nativeHeatStep_hBase_040_Gen]
  exact nativeHeat040All48

theorem nativeHeatResultGen_040 : nativeHeatResultGen 40 = nativeHeat040Result := by
  rw [← nativeHeat040Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_040_Gen, nativeHeatStep_hY0_040_Gen, nativeHeatStep_hExp_040_Gen,
    nativeHeatStep_hInit_040_Gen, nativeHeatStep_hFixed_040_Gen]

end ASDExplicitGamma.Native

end
