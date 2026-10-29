module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat096Complete
public import ASDExplicitGamma.Numerics.Native.Gap097Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_096_Gen : nativeHeatOldRowGen 96 = nativeGap097Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_096_Gen : nativeHeatIndividualGen 96 = nativeGap097Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_096_Gen : nativeHeatGenVariance 96 = nativeHeat096Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_096_Gen, nativeHeat096Variance_formula]

theorem nativeHeatStep_hSpec_096_Gen : nativeHeatGenSpectral 96 = nativeHeat096Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_096_Gen, nativeHeat096Variance_formula]

theorem nativeHeatStep_hQm_096_Gen : nativeHeatGenQm 96 = nativeHeat096Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_096_Gen, nativeHeatStep_hSpec_096_Gen,
    nativeHeat096Qm_formula]

theorem nativeHeatStep_hQN_096_Gen : nativeHeatQNGen 96 = nativeHeat096QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_096_Gen, nativeHeat096QN_formula]

theorem nativeHeatStep_hFr_096_Gen : nativeHeatFramesGen 96 = nativeHeat096Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_096_Gen, nativeHeatStep_hInd_096_Gen,
    nativeHeatStep_hVar_096_Gen, nativeHeatStep_hQN_096_Gen, nativeHeat096Frames_formula]

theorem nativeHeatStep_hArg_096_Gen : nativeHeatExpArgGen 96 = nativeHeatExpArg nativeGap097Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_096_Gen]

theorem nativeHeatStep_hExp_096_Gen : nativeHeatExpGen 96 = nativeHeat096Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_096_Gen, nativeHeat096Exp_formula]

theorem nativeHeatStep_hCoef_096_Gen : nativeHeatCoefGen 96 = nativeHeat096Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_096_Gen, nativeHeat096Coef_formula]

theorem nativeHeatStep_hInit_096_Gen : nativeHeatInitGen 96 = nativeHeat096Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_096_Gen, nativeHeatStep_hVar_096_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat096Init00_formula
    · exact nativeHeat096Init01_formula
    · exact nativeHeat096Init02_formula
    · exact nativeHeat096Init03_formula
    · exact nativeHeat096Init04_formula
    · exact nativeHeat096Init05_formula
    · exact nativeHeat096Init06_formula
    · exact nativeHeat096Init07_formula
    · exact nativeHeat096Init08_formula
    · exact nativeHeat096Init09_formula
    · exact nativeHeat096Init10_formula
    · exact nativeHeat096Init11_formula
    · exact nativeHeat096Init12_formula
    · exact nativeHeat096Init13_formula
    · exact nativeHeat096Init14_formula
    · exact nativeHeat096Init15_formula
    · exact nativeHeat096Init16_formula
    · exact nativeHeat096Init17_formula
    · exact nativeHeat096Init18_formula
    · exact nativeHeat096Init19_formula
    · exact nativeHeat096Init20_formula
theorem nativeHeatStep_hBase_096_Gen : nativeHeatBaseGen 96 = nativeHeat096Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_096_Gen, nativeHeatStep_hInit_096_Gen, nativeHeat096Base_formula]

theorem nativeHeatStep_hFixed_096_Gen : nativeHeatFixedGen 96 = nativeHeat096Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_096_Gen, nativeHeatStep_hFr_096_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat096Fixed01_formula
    · exact nativeHeat096Fixed02_formula
    · exact nativeHeat096Fixed03_formula
    · exact nativeHeat096Fixed04_formula
    · exact nativeHeat096Fixed05_formula
    · exact nativeHeat096Fixed06_formula
    · exact nativeHeat096Fixed07_formula
    · exact nativeHeat096Fixed08_formula
    · exact nativeHeat096Fixed09_formula
    · exact nativeHeat096Fixed10_formula
    · exact nativeHeat096Fixed11_formula
    · exact nativeHeat096Fixed12_formula
    · exact nativeHeat096Fixed13_formula
    · exact nativeHeat096Fixed14_formula
    · exact nativeHeat096Fixed15_formula
    · exact nativeHeat096Fixed16_formula
    · exact nativeHeat096Fixed17_formula
    · exact nativeHeat096Fixed18_formula
    · exact nativeHeat096Fixed19_formula
    · exact nativeHeat096Fixed20_formula

theorem nativeHeatStep_chk_096_Gen :
    nativeHeatPassRootsOk nativeGap097Old nativeHeat096Frames nativeHeat096Coef nativeHeat096Fixed nativeHeat096Base 48 nativeHeat096Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_096_Gen : NativeHeatStepPassNum 96 := by
  refine nativeHeatStepPassNum_of_literals 96 nativeGap097Old nativeHeat096Frames (nativeHeatExpArg nativeGap097Old)
    nativeHeat096Exp nativeHeat096Coef nativeHeat096Fixed nativeHeat096Init nativeHeat096Base nativeHeatStep_hOld_096_Gen
    nativeHeatStep_hFr_096_Gen nativeHeatStep_hArg_096_Gen nativeHeatStep_hExp_096_Gen
    nativeHeatStep_hCoef_096_Gen nativeHeatStep_hFixed_096_Gen
    nativeHeatStep_hInit_096_Gen nativeHeatStep_hBase_096_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_096_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_096_Gen :
    nativeHeatY0Gen 96 = nativeShiftedFrame 1 (min nativeGap097Old.x nativeGap097Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_096_Gen, nativeHeatStep_hInd_096_Gen]

theorem nativeHeatStepFrameNum_096_Gen : NativeHeatStepFrameNum 96 := by
  have h1 := nativeHeatStep_hOld_096_Gen
  have h2 := nativeHeatStep_hInd_096_Gen
  have h3 := nativeHeatStep_hVar_096_Gen
  have h4 := nativeHeatStep_hQm_096_Gen
  have h5 := nativeHeatStep_hQN_096_Gen
  have h6 := nativeHeatStep_hY0_096_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_096_Gen : NativeHeatStepIndivNum 96 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 96 (by norm_num)) = nativeGap097Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_096_Gen]; exact nativeGap097Old_source
  · rw [hc, nativeHeatStep_hInd_096_Gen]; exact nativeGap097Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_096_Gen : nativeHeatY48Gen 96 = nativeHeat096Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_096_Gen, nativeHeatStep_hFr_096_Gen,
    nativeHeatStep_hCoef_096_Gen, nativeHeatStep_hFixed_096_Gen,
    nativeHeatStep_hBase_096_Gen]
  exact nativeHeat096All48

theorem nativeHeatResultGen_096 : nativeHeatResultGen 96 = nativeHeat096Result := by
  rw [← nativeHeat096Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_096_Gen, nativeHeatStep_hY0_096_Gen, nativeHeatStep_hExp_096_Gen,
    nativeHeatStep_hInit_096_Gen, nativeHeatStep_hFixed_096_Gen]

end ASDExplicitGamma.Native

end
