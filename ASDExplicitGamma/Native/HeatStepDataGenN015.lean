module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat015Complete
public import ASDExplicitGamma.Numerics.Native.Gap016Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_015_Gen : nativeHeatOldRowGen 15 = nativeGap016Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_015_Gen : nativeHeatIndividualGen 15 = nativeGap016Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_015_Gen : nativeHeatGenVariance 15 = nativeHeat015Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_015_Gen, nativeHeat015Variance_formula]

theorem nativeHeatStep_hSpec_015_Gen : nativeHeatGenSpectral 15 = nativeHeat015Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_015_Gen, nativeHeat015Variance_formula]

theorem nativeHeatStep_hQm_015_Gen : nativeHeatGenQm 15 = nativeHeat015Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_015_Gen, nativeHeatStep_hSpec_015_Gen,
    nativeHeat015Qm_formula]

theorem nativeHeatStep_hQN_015_Gen : nativeHeatQNGen 15 = nativeHeat015QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_015_Gen, nativeHeat015QN_formula]

theorem nativeHeatStep_hFr_015_Gen : nativeHeatFramesGen 15 = nativeHeat015Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_015_Gen, nativeHeatStep_hInd_015_Gen,
    nativeHeatStep_hVar_015_Gen, nativeHeatStep_hQN_015_Gen, nativeHeat015Frames_formula]

theorem nativeHeatStep_hArg_015_Gen : nativeHeatExpArgGen 15 = nativeHeatExpArg nativeGap016Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_015_Gen]

theorem nativeHeatStep_hExp_015_Gen : nativeHeatExpGen 15 = nativeHeat015Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_015_Gen, nativeHeat015Exp_formula]

theorem nativeHeatStep_hCoef_015_Gen : nativeHeatCoefGen 15 = nativeHeat015Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_015_Gen, nativeHeat015Coef_formula]

theorem nativeHeatStep_hInit_015_Gen : nativeHeatInitGen 15 = nativeHeat015Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_015_Gen, nativeHeatStep_hVar_015_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat015Init00_formula
    · exact nativeHeat015Init01_formula
    · exact nativeHeat015Init02_formula
    · exact nativeHeat015Init03_formula
    · exact nativeHeat015Init04_formula
    · exact nativeHeat015Init05_formula
    · exact nativeHeat015Init06_formula
    · exact nativeHeat015Init07_formula
    · exact nativeHeat015Init08_formula
    · exact nativeHeat015Init09_formula
    · exact nativeHeat015Init10_formula
    · exact nativeHeat015Init11_formula
    · exact nativeHeat015Init12_formula
    · exact nativeHeat015Init13_formula
    · exact nativeHeat015Init14_formula
    · exact nativeHeat015Init15_formula
    · exact nativeHeat015Init16_formula
    · exact nativeHeat015Init17_formula
    · exact nativeHeat015Init18_formula
    · exact nativeHeat015Init19_formula
    · exact nativeHeat015Init20_formula
theorem nativeHeatStep_hBase_015_Gen : nativeHeatBaseGen 15 = nativeHeat015Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_015_Gen, nativeHeatStep_hInit_015_Gen, nativeHeat015Base_formula]

theorem nativeHeatStep_hFixed_015_Gen : nativeHeatFixedGen 15 = nativeHeat015Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_015_Gen, nativeHeatStep_hFr_015_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat015Fixed01_formula
    · exact nativeHeat015Fixed02_formula
    · exact nativeHeat015Fixed03_formula
    · exact nativeHeat015Fixed04_formula
    · exact nativeHeat015Fixed05_formula
    · exact nativeHeat015Fixed06_formula
    · exact nativeHeat015Fixed07_formula
    · exact nativeHeat015Fixed08_formula
    · exact nativeHeat015Fixed09_formula
    · exact nativeHeat015Fixed10_formula
    · exact nativeHeat015Fixed11_formula
    · exact nativeHeat015Fixed12_formula
    · exact nativeHeat015Fixed13_formula
    · exact nativeHeat015Fixed14_formula
    · exact nativeHeat015Fixed15_formula
    · exact nativeHeat015Fixed16_formula
    · exact nativeHeat015Fixed17_formula
    · exact nativeHeat015Fixed18_formula
    · exact nativeHeat015Fixed19_formula
    · exact nativeHeat015Fixed20_formula

theorem nativeHeatStep_chk_015_Gen :
    nativeHeatPassRootsOk nativeGap016Old nativeHeat015Frames nativeHeat015Coef nativeHeat015Fixed nativeHeat015Base 48 nativeHeat015Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_015_Gen : NativeHeatStepPassNum 15 := by
  refine nativeHeatStepPassNum_of_literals 15 nativeGap016Old nativeHeat015Frames (nativeHeatExpArg nativeGap016Old)
    nativeHeat015Exp nativeHeat015Coef nativeHeat015Fixed nativeHeat015Init nativeHeat015Base nativeHeatStep_hOld_015_Gen
    nativeHeatStep_hFr_015_Gen nativeHeatStep_hArg_015_Gen nativeHeatStep_hExp_015_Gen
    nativeHeatStep_hCoef_015_Gen nativeHeatStep_hFixed_015_Gen
    nativeHeatStep_hInit_015_Gen nativeHeatStep_hBase_015_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_015_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_015_Gen :
    nativeHeatY0Gen 15 = nativeShiftedFrame 1 (min nativeGap016Old.x nativeGap016Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_015_Gen, nativeHeatStep_hInd_015_Gen]

theorem nativeHeatStepFrameNum_015_Gen : NativeHeatStepFrameNum 15 := by
  have h1 := nativeHeatStep_hOld_015_Gen
  have h2 := nativeHeatStep_hInd_015_Gen
  have h3 := nativeHeatStep_hVar_015_Gen
  have h4 := nativeHeatStep_hQm_015_Gen
  have h5 := nativeHeatStep_hQN_015_Gen
  have h6 := nativeHeatStep_hY0_015_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_015_Gen : NativeHeatStepIndivNum 15 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 15 (by norm_num)) = nativeGap016Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_015_Gen]; exact nativeGap016Old_source
  · rw [hc, nativeHeatStep_hInd_015_Gen]; exact nativeGap016Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_015_Gen : nativeHeatY48Gen 15 = nativeHeat015Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_015_Gen, nativeHeatStep_hFr_015_Gen,
    nativeHeatStep_hCoef_015_Gen, nativeHeatStep_hFixed_015_Gen,
    nativeHeatStep_hBase_015_Gen]
  exact nativeHeat015All48

theorem nativeHeatResultGen_015 : nativeHeatResultGen 15 = nativeHeat015Result := by
  rw [← nativeHeat015Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_015_Gen, nativeHeatStep_hY0_015_Gen, nativeHeatStep_hExp_015_Gen,
    nativeHeatStep_hInit_015_Gen, nativeHeatStep_hFixed_015_Gen]

end ASDExplicitGamma.Native

end
