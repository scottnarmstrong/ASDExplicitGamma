module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat149Complete
public import ASDExplicitGamma.Numerics.Native.Gap150Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_149_Gen : nativeHeatOldRowGen 149 = nativeGap150Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_149_Gen : nativeHeatIndividualGen 149 = nativeGap150Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_149_Gen : nativeHeatGenVariance 149 = nativeHeat149Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_149_Gen, nativeHeat149Variance_formula]

theorem nativeHeatStep_hSpec_149_Gen : nativeHeatGenSpectral 149 = nativeHeat149Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_149_Gen, nativeHeat149Variance_formula]

theorem nativeHeatStep_hQm_149_Gen : nativeHeatGenQm 149 = nativeHeat149Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_149_Gen, nativeHeatStep_hSpec_149_Gen,
    nativeHeat149Qm_formula]

theorem nativeHeatStep_hQN_149_Gen : nativeHeatQNGen 149 = nativeHeat149QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_149_Gen, nativeHeat149QN_formula]

theorem nativeHeatStep_hFr_149_Gen : nativeHeatFramesGen 149 = nativeHeat149Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_149_Gen, nativeHeatStep_hInd_149_Gen,
    nativeHeatStep_hVar_149_Gen, nativeHeatStep_hQN_149_Gen, nativeHeat149Frames_formula]

theorem nativeHeatStep_hArg_149_Gen : nativeHeatExpArgGen 149 = nativeHeatExpArg nativeGap150Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_149_Gen]

theorem nativeHeatStep_hExp_149_Gen : nativeHeatExpGen 149 = nativeHeat149Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_149_Gen, nativeHeat149Exp_formula]

theorem nativeHeatStep_hCoef_149_Gen : nativeHeatCoefGen 149 = nativeHeat149Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_149_Gen, nativeHeat149Coef_formula]

theorem nativeHeatStep_hInit_149_Gen : nativeHeatInitGen 149 = nativeHeat149Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_149_Gen, nativeHeatStep_hVar_149_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat149Init00_formula
    · exact nativeHeat149Init01_formula
    · exact nativeHeat149Init02_formula
    · exact nativeHeat149Init03_formula
    · exact nativeHeat149Init04_formula
    · exact nativeHeat149Init05_formula
    · exact nativeHeat149Init06_formula
    · exact nativeHeat149Init07_formula
    · exact nativeHeat149Init08_formula
    · exact nativeHeat149Init09_formula
    · exact nativeHeat149Init10_formula
    · exact nativeHeat149Init11_formula
    · exact nativeHeat149Init12_formula
    · exact nativeHeat149Init13_formula
    · exact nativeHeat149Init14_formula
    · exact nativeHeat149Init15_formula
    · exact nativeHeat149Init16_formula
    · exact nativeHeat149Init17_formula
    · exact nativeHeat149Init18_formula
    · exact nativeHeat149Init19_formula
    · exact nativeHeat149Init20_formula
theorem nativeHeatStep_hBase_149_Gen : nativeHeatBaseGen 149 = nativeHeat149Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_149_Gen, nativeHeatStep_hInit_149_Gen, nativeHeat149Base_formula]

theorem nativeHeatStep_hFixed_149_Gen : nativeHeatFixedGen 149 = nativeHeat149Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_149_Gen, nativeHeatStep_hFr_149_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat149Fixed01_formula
    · exact nativeHeat149Fixed02_formula
    · exact nativeHeat149Fixed03_formula
    · exact nativeHeat149Fixed04_formula
    · exact nativeHeat149Fixed05_formula
    · exact nativeHeat149Fixed06_formula
    · exact nativeHeat149Fixed07_formula
    · exact nativeHeat149Fixed08_formula
    · exact nativeHeat149Fixed09_formula
    · exact nativeHeat149Fixed10_formula
    · exact nativeHeat149Fixed11_formula
    · exact nativeHeat149Fixed12_formula
    · exact nativeHeat149Fixed13_formula
    · exact nativeHeat149Fixed14_formula
    · exact nativeHeat149Fixed15_formula
    · exact nativeHeat149Fixed16_formula
    · exact nativeHeat149Fixed17_formula
    · exact nativeHeat149Fixed18_formula
    · exact nativeHeat149Fixed19_formula
    · exact nativeHeat149Fixed20_formula

theorem nativeHeatStep_chk_149_Gen :
    nativeHeatPassRootsOk nativeGap150Old nativeHeat149Frames nativeHeat149Coef nativeHeat149Fixed nativeHeat149Base 48 nativeHeat149Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_149_Gen : NativeHeatStepPassNum 149 := by
  refine nativeHeatStepPassNum_of_literals 149 nativeGap150Old nativeHeat149Frames (nativeHeatExpArg nativeGap150Old)
    nativeHeat149Exp nativeHeat149Coef nativeHeat149Fixed nativeHeat149Init nativeHeat149Base nativeHeatStep_hOld_149_Gen
    nativeHeatStep_hFr_149_Gen nativeHeatStep_hArg_149_Gen nativeHeatStep_hExp_149_Gen
    nativeHeatStep_hCoef_149_Gen nativeHeatStep_hFixed_149_Gen
    nativeHeatStep_hInit_149_Gen nativeHeatStep_hBase_149_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_149_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_149_Gen :
    nativeHeatY0Gen 149 = nativeShiftedFrame 1 (min nativeGap150Old.x nativeGap150Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_149_Gen, nativeHeatStep_hInd_149_Gen]

theorem nativeHeatStepFrameNum_149_Gen : NativeHeatStepFrameNum 149 := by
  have h1 := nativeHeatStep_hOld_149_Gen
  have h2 := nativeHeatStep_hInd_149_Gen
  have h3 := nativeHeatStep_hVar_149_Gen
  have h4 := nativeHeatStep_hQm_149_Gen
  have h5 := nativeHeatStep_hQN_149_Gen
  have h6 := nativeHeatStep_hY0_149_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_149_Gen : NativeHeatStepIndivNum 149 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 149 (by norm_num)) = nativeGap150Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_149_Gen]; exact nativeGap150Old_source
  · rw [hc, nativeHeatStep_hInd_149_Gen]; exact nativeGap150Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_149_Gen : nativeHeatY48Gen 149 = nativeHeat149Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_149_Gen, nativeHeatStep_hFr_149_Gen,
    nativeHeatStep_hCoef_149_Gen, nativeHeatStep_hFixed_149_Gen,
    nativeHeatStep_hBase_149_Gen]
  exact nativeHeat149All48

theorem nativeHeatResultGen_149 : nativeHeatResultGen 149 = nativeHeat149Result := by
  rw [← nativeHeat149Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_149_Gen, nativeHeatStep_hY0_149_Gen, nativeHeatStep_hExp_149_Gen,
    nativeHeatStep_hInit_149_Gen, nativeHeatStep_hFixed_149_Gen]

end ASDExplicitGamma.Native

end
