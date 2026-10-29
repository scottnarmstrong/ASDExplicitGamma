module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat147Complete
public import ASDExplicitGamma.Numerics.Native.Gap148Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_147_Gen : nativeHeatOldRowGen 147 = nativeGap148Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_147_Gen : nativeHeatIndividualGen 147 = nativeGap148Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_147_Gen : nativeHeatGenVariance 147 = nativeHeat147Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_147_Gen, nativeHeat147Variance_formula]

theorem nativeHeatStep_hSpec_147_Gen : nativeHeatGenSpectral 147 = nativeHeat147Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_147_Gen, nativeHeat147Variance_formula]

theorem nativeHeatStep_hQm_147_Gen : nativeHeatGenQm 147 = nativeHeat147Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_147_Gen, nativeHeatStep_hSpec_147_Gen,
    nativeHeat147Qm_formula]

theorem nativeHeatStep_hQN_147_Gen : nativeHeatQNGen 147 = nativeHeat147QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_147_Gen, nativeHeat147QN_formula]

theorem nativeHeatStep_hFr_147_Gen : nativeHeatFramesGen 147 = nativeHeat147Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_147_Gen, nativeHeatStep_hInd_147_Gen,
    nativeHeatStep_hVar_147_Gen, nativeHeatStep_hQN_147_Gen, nativeHeat147Frames_formula]

theorem nativeHeatStep_hArg_147_Gen : nativeHeatExpArgGen 147 = nativeHeatExpArg nativeGap148Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_147_Gen]

theorem nativeHeatStep_hExp_147_Gen : nativeHeatExpGen 147 = nativeHeat147Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_147_Gen, nativeHeat147Exp_formula]

theorem nativeHeatStep_hCoef_147_Gen : nativeHeatCoefGen 147 = nativeHeat147Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_147_Gen, nativeHeat147Coef_formula]

theorem nativeHeatStep_hInit_147_Gen : nativeHeatInitGen 147 = nativeHeat147Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_147_Gen, nativeHeatStep_hVar_147_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat147Init00_formula
    · exact nativeHeat147Init01_formula
    · exact nativeHeat147Init02_formula
    · exact nativeHeat147Init03_formula
    · exact nativeHeat147Init04_formula
    · exact nativeHeat147Init05_formula
    · exact nativeHeat147Init06_formula
    · exact nativeHeat147Init07_formula
    · exact nativeHeat147Init08_formula
    · exact nativeHeat147Init09_formula
    · exact nativeHeat147Init10_formula
    · exact nativeHeat147Init11_formula
    · exact nativeHeat147Init12_formula
    · exact nativeHeat147Init13_formula
    · exact nativeHeat147Init14_formula
    · exact nativeHeat147Init15_formula
    · exact nativeHeat147Init16_formula
    · exact nativeHeat147Init17_formula
    · exact nativeHeat147Init18_formula
    · exact nativeHeat147Init19_formula
    · exact nativeHeat147Init20_formula
theorem nativeHeatStep_hBase_147_Gen : nativeHeatBaseGen 147 = nativeHeat147Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_147_Gen, nativeHeatStep_hInit_147_Gen, nativeHeat147Base_formula]

theorem nativeHeatStep_hFixed_147_Gen : nativeHeatFixedGen 147 = nativeHeat147Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_147_Gen, nativeHeatStep_hFr_147_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat147Fixed01_formula
    · exact nativeHeat147Fixed02_formula
    · exact nativeHeat147Fixed03_formula
    · exact nativeHeat147Fixed04_formula
    · exact nativeHeat147Fixed05_formula
    · exact nativeHeat147Fixed06_formula
    · exact nativeHeat147Fixed07_formula
    · exact nativeHeat147Fixed08_formula
    · exact nativeHeat147Fixed09_formula
    · exact nativeHeat147Fixed10_formula
    · exact nativeHeat147Fixed11_formula
    · exact nativeHeat147Fixed12_formula
    · exact nativeHeat147Fixed13_formula
    · exact nativeHeat147Fixed14_formula
    · exact nativeHeat147Fixed15_formula
    · exact nativeHeat147Fixed16_formula
    · exact nativeHeat147Fixed17_formula
    · exact nativeHeat147Fixed18_formula
    · exact nativeHeat147Fixed19_formula
    · exact nativeHeat147Fixed20_formula

theorem nativeHeatStep_chk_147_Gen :
    nativeHeatPassRootsOk nativeGap148Old nativeHeat147Frames nativeHeat147Coef nativeHeat147Fixed nativeHeat147Base 48 nativeHeat147Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_147_Gen : NativeHeatStepPassNum 147 := by
  refine nativeHeatStepPassNum_of_literals 147 nativeGap148Old nativeHeat147Frames (nativeHeatExpArg nativeGap148Old)
    nativeHeat147Exp nativeHeat147Coef nativeHeat147Fixed nativeHeat147Init nativeHeat147Base nativeHeatStep_hOld_147_Gen
    nativeHeatStep_hFr_147_Gen nativeHeatStep_hArg_147_Gen nativeHeatStep_hExp_147_Gen
    nativeHeatStep_hCoef_147_Gen nativeHeatStep_hFixed_147_Gen
    nativeHeatStep_hInit_147_Gen nativeHeatStep_hBase_147_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_147_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_147_Gen :
    nativeHeatY0Gen 147 = nativeShiftedFrame 1 (min nativeGap148Old.x nativeGap148Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_147_Gen, nativeHeatStep_hInd_147_Gen]

theorem nativeHeatStepFrameNum_147_Gen : NativeHeatStepFrameNum 147 := by
  have h1 := nativeHeatStep_hOld_147_Gen
  have h2 := nativeHeatStep_hInd_147_Gen
  have h3 := nativeHeatStep_hVar_147_Gen
  have h4 := nativeHeatStep_hQm_147_Gen
  have h5 := nativeHeatStep_hQN_147_Gen
  have h6 := nativeHeatStep_hY0_147_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_147_Gen : NativeHeatStepIndivNum 147 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 147 (by norm_num)) = nativeGap148Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_147_Gen]; exact nativeGap148Old_source
  · rw [hc, nativeHeatStep_hInd_147_Gen]; exact nativeGap148Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_147_Gen : nativeHeatY48Gen 147 = nativeHeat147Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_147_Gen, nativeHeatStep_hFr_147_Gen,
    nativeHeatStep_hCoef_147_Gen, nativeHeatStep_hFixed_147_Gen,
    nativeHeatStep_hBase_147_Gen]
  exact nativeHeat147All48

theorem nativeHeatResultGen_147 : nativeHeatResultGen 147 = nativeHeat147Result := by
  rw [← nativeHeat147Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_147_Gen, nativeHeatStep_hY0_147_Gen, nativeHeatStep_hExp_147_Gen,
    nativeHeatStep_hInit_147_Gen, nativeHeatStep_hFixed_147_Gen]

end ASDExplicitGamma.Native

end
