module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat016Complete
public import ASDExplicitGamma.Numerics.Native.Gap017Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_016_Gen : nativeHeatOldRowGen 16 = nativeGap017Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_016_Gen : nativeHeatIndividualGen 16 = nativeGap017Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_016_Gen : nativeHeatGenVariance 16 = nativeHeat016Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_016_Gen, nativeHeat016Variance_formula]

theorem nativeHeatStep_hSpec_016_Gen : nativeHeatGenSpectral 16 = nativeHeat016Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_016_Gen, nativeHeat016Variance_formula]

theorem nativeHeatStep_hQm_016_Gen : nativeHeatGenQm 16 = nativeHeat016Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_016_Gen, nativeHeatStep_hSpec_016_Gen,
    nativeHeat016Qm_formula]

theorem nativeHeatStep_hQN_016_Gen : nativeHeatQNGen 16 = nativeHeat016QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_016_Gen, nativeHeat016QN_formula]

theorem nativeHeatStep_hFr_016_Gen : nativeHeatFramesGen 16 = nativeHeat016Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_016_Gen, nativeHeatStep_hInd_016_Gen,
    nativeHeatStep_hVar_016_Gen, nativeHeatStep_hQN_016_Gen, nativeHeat016Frames_formula]

theorem nativeHeatStep_hArg_016_Gen : nativeHeatExpArgGen 16 = nativeHeatExpArg nativeGap017Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_016_Gen]

theorem nativeHeatStep_hExp_016_Gen : nativeHeatExpGen 16 = nativeHeat016Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_016_Gen, nativeHeat016Exp_formula]

theorem nativeHeatStep_hCoef_016_Gen : nativeHeatCoefGen 16 = nativeHeat016Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_016_Gen, nativeHeat016Coef_formula]

theorem nativeHeatStep_hInit_016_Gen : nativeHeatInitGen 16 = nativeHeat016Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_016_Gen, nativeHeatStep_hVar_016_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat016Init00_formula
    · exact nativeHeat016Init01_formula
    · exact nativeHeat016Init02_formula
    · exact nativeHeat016Init03_formula
    · exact nativeHeat016Init04_formula
    · exact nativeHeat016Init05_formula
    · exact nativeHeat016Init06_formula
    · exact nativeHeat016Init07_formula
    · exact nativeHeat016Init08_formula
    · exact nativeHeat016Init09_formula
    · exact nativeHeat016Init10_formula
    · exact nativeHeat016Init11_formula
    · exact nativeHeat016Init12_formula
    · exact nativeHeat016Init13_formula
    · exact nativeHeat016Init14_formula
    · exact nativeHeat016Init15_formula
    · exact nativeHeat016Init16_formula
    · exact nativeHeat016Init17_formula
    · exact nativeHeat016Init18_formula
    · exact nativeHeat016Init19_formula
    · exact nativeHeat016Init20_formula
theorem nativeHeatStep_hBase_016_Gen : nativeHeatBaseGen 16 = nativeHeat016Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_016_Gen, nativeHeatStep_hInit_016_Gen, nativeHeat016Base_formula]

theorem nativeHeatStep_hFixed_016_Gen : nativeHeatFixedGen 16 = nativeHeat016Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_016_Gen, nativeHeatStep_hFr_016_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat016Fixed01_formula
    · exact nativeHeat016Fixed02_formula
    · exact nativeHeat016Fixed03_formula
    · exact nativeHeat016Fixed04_formula
    · exact nativeHeat016Fixed05_formula
    · exact nativeHeat016Fixed06_formula
    · exact nativeHeat016Fixed07_formula
    · exact nativeHeat016Fixed08_formula
    · exact nativeHeat016Fixed09_formula
    · exact nativeHeat016Fixed10_formula
    · exact nativeHeat016Fixed11_formula
    · exact nativeHeat016Fixed12_formula
    · exact nativeHeat016Fixed13_formula
    · exact nativeHeat016Fixed14_formula
    · exact nativeHeat016Fixed15_formula
    · exact nativeHeat016Fixed16_formula
    · exact nativeHeat016Fixed17_formula
    · exact nativeHeat016Fixed18_formula
    · exact nativeHeat016Fixed19_formula
    · exact nativeHeat016Fixed20_formula

theorem nativeHeatStep_chk_016_Gen :
    nativeHeatPassRootsOk nativeGap017Old nativeHeat016Frames nativeHeat016Coef nativeHeat016Fixed nativeHeat016Base 48 nativeHeat016Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_016_Gen : NativeHeatStepPassNum 16 := by
  refine nativeHeatStepPassNum_of_literals 16 nativeGap017Old nativeHeat016Frames (nativeHeatExpArg nativeGap017Old)
    nativeHeat016Exp nativeHeat016Coef nativeHeat016Fixed nativeHeat016Init nativeHeat016Base nativeHeatStep_hOld_016_Gen
    nativeHeatStep_hFr_016_Gen nativeHeatStep_hArg_016_Gen nativeHeatStep_hExp_016_Gen
    nativeHeatStep_hCoef_016_Gen nativeHeatStep_hFixed_016_Gen
    nativeHeatStep_hInit_016_Gen nativeHeatStep_hBase_016_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_016_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_016_Gen :
    nativeHeatY0Gen 16 = nativeShiftedFrame 1 (min nativeGap017Old.x nativeGap017Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_016_Gen, nativeHeatStep_hInd_016_Gen]

theorem nativeHeatStepFrameNum_016_Gen : NativeHeatStepFrameNum 16 := by
  have h1 := nativeHeatStep_hOld_016_Gen
  have h2 := nativeHeatStep_hInd_016_Gen
  have h3 := nativeHeatStep_hVar_016_Gen
  have h4 := nativeHeatStep_hQm_016_Gen
  have h5 := nativeHeatStep_hQN_016_Gen
  have h6 := nativeHeatStep_hY0_016_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_016_Gen : NativeHeatStepIndivNum 16 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 16 (by norm_num)) = nativeGap017Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_016_Gen]; exact nativeGap017Old_source
  · rw [hc, nativeHeatStep_hInd_016_Gen]; exact nativeGap017Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_016_Gen : nativeHeatY48Gen 16 = nativeHeat016Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_016_Gen, nativeHeatStep_hFr_016_Gen,
    nativeHeatStep_hCoef_016_Gen, nativeHeatStep_hFixed_016_Gen,
    nativeHeatStep_hBase_016_Gen]
  exact nativeHeat016All48

theorem nativeHeatResultGen_016 : nativeHeatResultGen 16 = nativeHeat016Result := by
  rw [← nativeHeat016Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_016_Gen, nativeHeatStep_hY0_016_Gen, nativeHeatStep_hExp_016_Gen,
    nativeHeatStep_hInit_016_Gen, nativeHeatStep_hFixed_016_Gen]

end ASDExplicitGamma.Native

end
