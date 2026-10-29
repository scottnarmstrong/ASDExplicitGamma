module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat055Complete
public import ASDExplicitGamma.Numerics.Native.Gap056Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_055_Gen : nativeHeatOldRowGen 55 = nativeGap056Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_055_Gen : nativeHeatIndividualGen 55 = nativeGap056Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_055_Gen : nativeHeatGenVariance 55 = nativeHeat055Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_055_Gen, nativeHeat055Variance_formula]

theorem nativeHeatStep_hSpec_055_Gen : nativeHeatGenSpectral 55 = nativeHeat055Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_055_Gen, nativeHeat055Variance_formula]

theorem nativeHeatStep_hQm_055_Gen : nativeHeatGenQm 55 = nativeHeat055Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_055_Gen, nativeHeatStep_hSpec_055_Gen,
    nativeHeat055Qm_formula]

theorem nativeHeatStep_hQN_055_Gen : nativeHeatQNGen 55 = nativeHeat055QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_055_Gen, nativeHeat055QN_formula]

theorem nativeHeatStep_hFr_055_Gen : nativeHeatFramesGen 55 = nativeHeat055Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_055_Gen, nativeHeatStep_hInd_055_Gen,
    nativeHeatStep_hVar_055_Gen, nativeHeatStep_hQN_055_Gen, nativeHeat055Frames_formula]

theorem nativeHeatStep_hArg_055_Gen : nativeHeatExpArgGen 55 = nativeHeatExpArg nativeGap056Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_055_Gen]

theorem nativeHeatStep_hExp_055_Gen : nativeHeatExpGen 55 = nativeHeat055Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_055_Gen, nativeHeat055Exp_formula]

theorem nativeHeatStep_hCoef_055_Gen : nativeHeatCoefGen 55 = nativeHeat055Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_055_Gen, nativeHeat055Coef_formula]

theorem nativeHeatStep_hInit_055_Gen : nativeHeatInitGen 55 = nativeHeat055Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_055_Gen, nativeHeatStep_hVar_055_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat055Init00_formula
    · exact nativeHeat055Init01_formula
    · exact nativeHeat055Init02_formula
    · exact nativeHeat055Init03_formula
    · exact nativeHeat055Init04_formula
    · exact nativeHeat055Init05_formula
    · exact nativeHeat055Init06_formula
    · exact nativeHeat055Init07_formula
    · exact nativeHeat055Init08_formula
    · exact nativeHeat055Init09_formula
    · exact nativeHeat055Init10_formula
    · exact nativeHeat055Init11_formula
    · exact nativeHeat055Init12_formula
    · exact nativeHeat055Init13_formula
    · exact nativeHeat055Init14_formula
    · exact nativeHeat055Init15_formula
    · exact nativeHeat055Init16_formula
    · exact nativeHeat055Init17_formula
    · exact nativeHeat055Init18_formula
    · exact nativeHeat055Init19_formula
    · exact nativeHeat055Init20_formula
theorem nativeHeatStep_hBase_055_Gen : nativeHeatBaseGen 55 = nativeHeat055Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_055_Gen, nativeHeatStep_hInit_055_Gen, nativeHeat055Base_formula]

theorem nativeHeatStep_hFixed_055_Gen : nativeHeatFixedGen 55 = nativeHeat055Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_055_Gen, nativeHeatStep_hFr_055_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat055Fixed01_formula
    · exact nativeHeat055Fixed02_formula
    · exact nativeHeat055Fixed03_formula
    · exact nativeHeat055Fixed04_formula
    · exact nativeHeat055Fixed05_formula
    · exact nativeHeat055Fixed06_formula
    · exact nativeHeat055Fixed07_formula
    · exact nativeHeat055Fixed08_formula
    · exact nativeHeat055Fixed09_formula
    · exact nativeHeat055Fixed10_formula
    · exact nativeHeat055Fixed11_formula
    · exact nativeHeat055Fixed12_formula
    · exact nativeHeat055Fixed13_formula
    · exact nativeHeat055Fixed14_formula
    · exact nativeHeat055Fixed15_formula
    · exact nativeHeat055Fixed16_formula
    · exact nativeHeat055Fixed17_formula
    · exact nativeHeat055Fixed18_formula
    · exact nativeHeat055Fixed19_formula
    · exact nativeHeat055Fixed20_formula

theorem nativeHeatStep_chk_055_Gen :
    nativeHeatPassRootsOk nativeGap056Old nativeHeat055Frames nativeHeat055Coef nativeHeat055Fixed nativeHeat055Base 48 nativeHeat055Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_055_Gen : NativeHeatStepPassNum 55 := by
  refine nativeHeatStepPassNum_of_literals 55 nativeGap056Old nativeHeat055Frames (nativeHeatExpArg nativeGap056Old)
    nativeHeat055Exp nativeHeat055Coef nativeHeat055Fixed nativeHeat055Init nativeHeat055Base nativeHeatStep_hOld_055_Gen
    nativeHeatStep_hFr_055_Gen nativeHeatStep_hArg_055_Gen nativeHeatStep_hExp_055_Gen
    nativeHeatStep_hCoef_055_Gen nativeHeatStep_hFixed_055_Gen
    nativeHeatStep_hInit_055_Gen nativeHeatStep_hBase_055_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_055_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_055_Gen :
    nativeHeatY0Gen 55 = nativeShiftedFrame 1 (min nativeGap056Old.x nativeGap056Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_055_Gen, nativeHeatStep_hInd_055_Gen]

theorem nativeHeatStepFrameNum_055_Gen : NativeHeatStepFrameNum 55 := by
  have h1 := nativeHeatStep_hOld_055_Gen
  have h2 := nativeHeatStep_hInd_055_Gen
  have h3 := nativeHeatStep_hVar_055_Gen
  have h4 := nativeHeatStep_hQm_055_Gen
  have h5 := nativeHeatStep_hQN_055_Gen
  have h6 := nativeHeatStep_hY0_055_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_055_Gen : NativeHeatStepIndivNum 55 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 55 (by norm_num)) = nativeGap056Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_055_Gen]; exact nativeGap056Old_source
  · rw [hc, nativeHeatStep_hInd_055_Gen]; exact nativeGap056Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_055_Gen : nativeHeatY48Gen 55 = nativeHeat055Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_055_Gen, nativeHeatStep_hFr_055_Gen,
    nativeHeatStep_hCoef_055_Gen, nativeHeatStep_hFixed_055_Gen,
    nativeHeatStep_hBase_055_Gen]
  exact nativeHeat055All48

theorem nativeHeatResultGen_055 : nativeHeatResultGen 55 = nativeHeat055Result := by
  rw [← nativeHeat055Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_055_Gen, nativeHeatStep_hY0_055_Gen, nativeHeatStep_hExp_055_Gen,
    nativeHeatStep_hInit_055_Gen, nativeHeatStep_hFixed_055_Gen]

end ASDExplicitGamma.Native

end
