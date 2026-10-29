module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat160Complete
public import ASDExplicitGamma.Numerics.Native.Gap161Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_160_Gen : nativeHeatOldRowGen 160 = nativeGap161Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_160_Gen : nativeHeatIndividualGen 160 = nativeGap161Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_160_Gen : nativeHeatGenVariance 160 = nativeHeat160Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_160_Gen, nativeHeat160Variance_formula]

theorem nativeHeatStep_hSpec_160_Gen : nativeHeatGenSpectral 160 = nativeHeat160Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_160_Gen, nativeHeat160Variance_formula]

theorem nativeHeatStep_hQm_160_Gen : nativeHeatGenQm 160 = nativeHeat160Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_160_Gen, nativeHeatStep_hSpec_160_Gen,
    nativeHeat160Qm_formula]

theorem nativeHeatStep_hQN_160_Gen : nativeHeatQNGen 160 = nativeHeat160QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_160_Gen, nativeHeat160QN_formula]

theorem nativeHeatStep_hFr_160_Gen : nativeHeatFramesGen 160 = nativeHeat160Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_160_Gen, nativeHeatStep_hInd_160_Gen,
    nativeHeatStep_hVar_160_Gen, nativeHeatStep_hQN_160_Gen, nativeHeat160Frames_formula]

theorem nativeHeatStep_hArg_160_Gen : nativeHeatExpArgGen 160 = nativeHeatExpArg nativeGap161Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_160_Gen]

theorem nativeHeatStep_hExp_160_Gen : nativeHeatExpGen 160 = nativeHeat160Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_160_Gen, nativeHeat160Exp_formula]

theorem nativeHeatStep_hCoef_160_Gen : nativeHeatCoefGen 160 = nativeHeat160Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_160_Gen, nativeHeat160Coef_formula]

theorem nativeHeatStep_hInit_160_Gen : nativeHeatInitGen 160 = nativeHeat160Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_160_Gen, nativeHeatStep_hVar_160_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat160Init00_formula
    · exact nativeHeat160Init01_formula
    · exact nativeHeat160Init02_formula
    · exact nativeHeat160Init03_formula
    · exact nativeHeat160Init04_formula
    · exact nativeHeat160Init05_formula
    · exact nativeHeat160Init06_formula
    · exact nativeHeat160Init07_formula
    · exact nativeHeat160Init08_formula
    · exact nativeHeat160Init09_formula
    · exact nativeHeat160Init10_formula
    · exact nativeHeat160Init11_formula
    · exact nativeHeat160Init12_formula
    · exact nativeHeat160Init13_formula
    · exact nativeHeat160Init14_formula
    · exact nativeHeat160Init15_formula
    · exact nativeHeat160Init16_formula
    · exact nativeHeat160Init17_formula
    · exact nativeHeat160Init18_formula
    · exact nativeHeat160Init19_formula
    · exact nativeHeat160Init20_formula
theorem nativeHeatStep_hBase_160_Gen : nativeHeatBaseGen 160 = nativeHeat160Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_160_Gen, nativeHeatStep_hInit_160_Gen, nativeHeat160Base_formula]

theorem nativeHeatStep_hFixed_160_Gen : nativeHeatFixedGen 160 = nativeHeat160Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_160_Gen, nativeHeatStep_hFr_160_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat160Fixed01_formula
    · exact nativeHeat160Fixed02_formula
    · exact nativeHeat160Fixed03_formula
    · exact nativeHeat160Fixed04_formula
    · exact nativeHeat160Fixed05_formula
    · exact nativeHeat160Fixed06_formula
    · exact nativeHeat160Fixed07_formula
    · exact nativeHeat160Fixed08_formula
    · exact nativeHeat160Fixed09_formula
    · exact nativeHeat160Fixed10_formula
    · exact nativeHeat160Fixed11_formula
    · exact nativeHeat160Fixed12_formula
    · exact nativeHeat160Fixed13_formula
    · exact nativeHeat160Fixed14_formula
    · exact nativeHeat160Fixed15_formula
    · exact nativeHeat160Fixed16_formula
    · exact nativeHeat160Fixed17_formula
    · exact nativeHeat160Fixed18_formula
    · exact nativeHeat160Fixed19_formula
    · exact nativeHeat160Fixed20_formula

theorem nativeHeatStep_chk_160_Gen :
    nativeHeatPassRootsOk nativeGap161Old nativeHeat160Frames nativeHeat160Coef nativeHeat160Fixed nativeHeat160Base 48 nativeHeat160Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_160_Gen : NativeHeatStepPassNum 160 := by
  refine nativeHeatStepPassNum_of_literals 160 nativeGap161Old nativeHeat160Frames (nativeHeatExpArg nativeGap161Old)
    nativeHeat160Exp nativeHeat160Coef nativeHeat160Fixed nativeHeat160Init nativeHeat160Base nativeHeatStep_hOld_160_Gen
    nativeHeatStep_hFr_160_Gen nativeHeatStep_hArg_160_Gen nativeHeatStep_hExp_160_Gen
    nativeHeatStep_hCoef_160_Gen nativeHeatStep_hFixed_160_Gen
    nativeHeatStep_hInit_160_Gen nativeHeatStep_hBase_160_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_160_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_160_Gen :
    nativeHeatY0Gen 160 = nativeShiftedFrame 1 (min nativeGap161Old.x nativeGap161Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_160_Gen, nativeHeatStep_hInd_160_Gen]

theorem nativeHeatStepFrameNum_160_Gen : NativeHeatStepFrameNum 160 := by
  have h1 := nativeHeatStep_hOld_160_Gen
  have h2 := nativeHeatStep_hInd_160_Gen
  have h3 := nativeHeatStep_hVar_160_Gen
  have h4 := nativeHeatStep_hQm_160_Gen
  have h5 := nativeHeatStep_hQN_160_Gen
  have h6 := nativeHeatStep_hY0_160_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_160_Gen : NativeHeatStepIndivNum 160 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 160 (by norm_num)) = nativeGap161Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_160_Gen]; exact nativeGap161Old_source
  · rw [hc, nativeHeatStep_hInd_160_Gen]; exact nativeGap161Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_160_Gen : nativeHeatY48Gen 160 = nativeHeat160Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_160_Gen, nativeHeatStep_hFr_160_Gen,
    nativeHeatStep_hCoef_160_Gen, nativeHeatStep_hFixed_160_Gen,
    nativeHeatStep_hBase_160_Gen]
  exact nativeHeat160All48

theorem nativeHeatResultGen_160 : nativeHeatResultGen 160 = nativeHeat160Result := by
  rw [← nativeHeat160Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_160_Gen, nativeHeatStep_hY0_160_Gen, nativeHeatStep_hExp_160_Gen,
    nativeHeatStep_hInit_160_Gen, nativeHeatStep_hFixed_160_Gen]

end ASDExplicitGamma.Native

end
