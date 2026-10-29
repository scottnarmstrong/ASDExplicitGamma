module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat078Complete
public import ASDExplicitGamma.Numerics.Native.Gap079Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_078_Gen : nativeHeatOldRowGen 78 = nativeGap079Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_078_Gen : nativeHeatIndividualGen 78 = nativeGap079Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_078_Gen : nativeHeatGenVariance 78 = nativeHeat078Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_078_Gen, nativeHeat078Variance_formula]

theorem nativeHeatStep_hSpec_078_Gen : nativeHeatGenSpectral 78 = nativeHeat078Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_078_Gen, nativeHeat078Variance_formula]

theorem nativeHeatStep_hQm_078_Gen : nativeHeatGenQm 78 = nativeHeat078Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_078_Gen, nativeHeatStep_hSpec_078_Gen,
    nativeHeat078Qm_formula]

theorem nativeHeatStep_hQN_078_Gen : nativeHeatQNGen 78 = nativeHeat078QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_078_Gen, nativeHeat078QN_formula]

theorem nativeHeatStep_hFr_078_Gen : nativeHeatFramesGen 78 = nativeHeat078Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_078_Gen, nativeHeatStep_hInd_078_Gen,
    nativeHeatStep_hVar_078_Gen, nativeHeatStep_hQN_078_Gen, nativeHeat078Frames_formula]

theorem nativeHeatStep_hArg_078_Gen : nativeHeatExpArgGen 78 = nativeHeatExpArg nativeGap079Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_078_Gen]

theorem nativeHeatStep_hExp_078_Gen : nativeHeatExpGen 78 = nativeHeat078Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_078_Gen, nativeHeat078Exp_formula]

theorem nativeHeatStep_hCoef_078_Gen : nativeHeatCoefGen 78 = nativeHeat078Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_078_Gen, nativeHeat078Coef_formula]

theorem nativeHeatStep_hInit_078_Gen : nativeHeatInitGen 78 = nativeHeat078Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_078_Gen, nativeHeatStep_hVar_078_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat078Init00_formula
    · exact nativeHeat078Init01_formula
    · exact nativeHeat078Init02_formula
    · exact nativeHeat078Init03_formula
    · exact nativeHeat078Init04_formula
    · exact nativeHeat078Init05_formula
    · exact nativeHeat078Init06_formula
    · exact nativeHeat078Init07_formula
    · exact nativeHeat078Init08_formula
    · exact nativeHeat078Init09_formula
    · exact nativeHeat078Init10_formula
    · exact nativeHeat078Init11_formula
    · exact nativeHeat078Init12_formula
    · exact nativeHeat078Init13_formula
    · exact nativeHeat078Init14_formula
    · exact nativeHeat078Init15_formula
    · exact nativeHeat078Init16_formula
    · exact nativeHeat078Init17_formula
    · exact nativeHeat078Init18_formula
    · exact nativeHeat078Init19_formula
    · exact nativeHeat078Init20_formula
theorem nativeHeatStep_hBase_078_Gen : nativeHeatBaseGen 78 = nativeHeat078Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_078_Gen, nativeHeatStep_hInit_078_Gen, nativeHeat078Base_formula]

theorem nativeHeatStep_hFixed_078_Gen : nativeHeatFixedGen 78 = nativeHeat078Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_078_Gen, nativeHeatStep_hFr_078_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat078Fixed01_formula
    · exact nativeHeat078Fixed02_formula
    · exact nativeHeat078Fixed03_formula
    · exact nativeHeat078Fixed04_formula
    · exact nativeHeat078Fixed05_formula
    · exact nativeHeat078Fixed06_formula
    · exact nativeHeat078Fixed07_formula
    · exact nativeHeat078Fixed08_formula
    · exact nativeHeat078Fixed09_formula
    · exact nativeHeat078Fixed10_formula
    · exact nativeHeat078Fixed11_formula
    · exact nativeHeat078Fixed12_formula
    · exact nativeHeat078Fixed13_formula
    · exact nativeHeat078Fixed14_formula
    · exact nativeHeat078Fixed15_formula
    · exact nativeHeat078Fixed16_formula
    · exact nativeHeat078Fixed17_formula
    · exact nativeHeat078Fixed18_formula
    · exact nativeHeat078Fixed19_formula
    · exact nativeHeat078Fixed20_formula

theorem nativeHeatStep_chk_078_Gen :
    nativeHeatPassRootsOk nativeGap079Old nativeHeat078Frames nativeHeat078Coef nativeHeat078Fixed nativeHeat078Base 48 nativeHeat078Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_078_Gen : NativeHeatStepPassNum 78 := by
  refine nativeHeatStepPassNum_of_literals 78 nativeGap079Old nativeHeat078Frames (nativeHeatExpArg nativeGap079Old)
    nativeHeat078Exp nativeHeat078Coef nativeHeat078Fixed nativeHeat078Init nativeHeat078Base nativeHeatStep_hOld_078_Gen
    nativeHeatStep_hFr_078_Gen nativeHeatStep_hArg_078_Gen nativeHeatStep_hExp_078_Gen
    nativeHeatStep_hCoef_078_Gen nativeHeatStep_hFixed_078_Gen
    nativeHeatStep_hInit_078_Gen nativeHeatStep_hBase_078_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_078_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_078_Gen :
    nativeHeatY0Gen 78 = nativeShiftedFrame 1 (min nativeGap079Old.x nativeGap079Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_078_Gen, nativeHeatStep_hInd_078_Gen]

theorem nativeHeatStepFrameNum_078_Gen : NativeHeatStepFrameNum 78 := by
  have h1 := nativeHeatStep_hOld_078_Gen
  have h2 := nativeHeatStep_hInd_078_Gen
  have h3 := nativeHeatStep_hVar_078_Gen
  have h4 := nativeHeatStep_hQm_078_Gen
  have h5 := nativeHeatStep_hQN_078_Gen
  have h6 := nativeHeatStep_hY0_078_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_078_Gen : NativeHeatStepIndivNum 78 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 78 (by norm_num)) = nativeGap079Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_078_Gen]; exact nativeGap079Old_source
  · rw [hc, nativeHeatStep_hInd_078_Gen]; exact nativeGap079Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_078_Gen : nativeHeatY48Gen 78 = nativeHeat078Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_078_Gen, nativeHeatStep_hFr_078_Gen,
    nativeHeatStep_hCoef_078_Gen, nativeHeatStep_hFixed_078_Gen,
    nativeHeatStep_hBase_078_Gen]
  exact nativeHeat078All48

theorem nativeHeatResultGen_078 : nativeHeatResultGen 78 = nativeHeat078Result := by
  rw [← nativeHeat078Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_078_Gen, nativeHeatStep_hY0_078_Gen, nativeHeatStep_hExp_078_Gen,
    nativeHeatStep_hInit_078_Gen, nativeHeatStep_hFixed_078_Gen]

end ASDExplicitGamma.Native

end
