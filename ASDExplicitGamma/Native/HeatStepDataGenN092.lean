module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat092Complete
public import ASDExplicitGamma.Numerics.Native.Gap093Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_092_Gen : nativeHeatOldRowGen 92 = nativeGap093Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_092_Gen : nativeHeatIndividualGen 92 = nativeGap093Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_092_Gen : nativeHeatGenVariance 92 = nativeHeat092Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_092_Gen, nativeHeat092Variance_formula]

theorem nativeHeatStep_hSpec_092_Gen : nativeHeatGenSpectral 92 = nativeHeat092Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_092_Gen, nativeHeat092Variance_formula]

theorem nativeHeatStep_hQm_092_Gen : nativeHeatGenQm 92 = nativeHeat092Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_092_Gen, nativeHeatStep_hSpec_092_Gen,
    nativeHeat092Qm_formula]

theorem nativeHeatStep_hQN_092_Gen : nativeHeatQNGen 92 = nativeHeat092QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_092_Gen, nativeHeat092QN_formula]

theorem nativeHeatStep_hFr_092_Gen : nativeHeatFramesGen 92 = nativeHeat092Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_092_Gen, nativeHeatStep_hInd_092_Gen,
    nativeHeatStep_hVar_092_Gen, nativeHeatStep_hQN_092_Gen, nativeHeat092Frames_formula]

theorem nativeHeatStep_hArg_092_Gen : nativeHeatExpArgGen 92 = nativeHeatExpArg nativeGap093Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_092_Gen]

theorem nativeHeatStep_hExp_092_Gen : nativeHeatExpGen 92 = nativeHeat092Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_092_Gen, nativeHeat092Exp_formula]

theorem nativeHeatStep_hCoef_092_Gen : nativeHeatCoefGen 92 = nativeHeat092Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_092_Gen, nativeHeat092Coef_formula]

theorem nativeHeatStep_hInit_092_Gen : nativeHeatInitGen 92 = nativeHeat092Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_092_Gen, nativeHeatStep_hVar_092_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat092Init00_formula
    · exact nativeHeat092Init01_formula
    · exact nativeHeat092Init02_formula
    · exact nativeHeat092Init03_formula
    · exact nativeHeat092Init04_formula
    · exact nativeHeat092Init05_formula
    · exact nativeHeat092Init06_formula
    · exact nativeHeat092Init07_formula
    · exact nativeHeat092Init08_formula
    · exact nativeHeat092Init09_formula
    · exact nativeHeat092Init10_formula
    · exact nativeHeat092Init11_formula
    · exact nativeHeat092Init12_formula
    · exact nativeHeat092Init13_formula
    · exact nativeHeat092Init14_formula
    · exact nativeHeat092Init15_formula
    · exact nativeHeat092Init16_formula
    · exact nativeHeat092Init17_formula
    · exact nativeHeat092Init18_formula
    · exact nativeHeat092Init19_formula
    · exact nativeHeat092Init20_formula
theorem nativeHeatStep_hBase_092_Gen : nativeHeatBaseGen 92 = nativeHeat092Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_092_Gen, nativeHeatStep_hInit_092_Gen, nativeHeat092Base_formula]

theorem nativeHeatStep_hFixed_092_Gen : nativeHeatFixedGen 92 = nativeHeat092Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_092_Gen, nativeHeatStep_hFr_092_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat092Fixed01_formula
    · exact nativeHeat092Fixed02_formula
    · exact nativeHeat092Fixed03_formula
    · exact nativeHeat092Fixed04_formula
    · exact nativeHeat092Fixed05_formula
    · exact nativeHeat092Fixed06_formula
    · exact nativeHeat092Fixed07_formula
    · exact nativeHeat092Fixed08_formula
    · exact nativeHeat092Fixed09_formula
    · exact nativeHeat092Fixed10_formula
    · exact nativeHeat092Fixed11_formula
    · exact nativeHeat092Fixed12_formula
    · exact nativeHeat092Fixed13_formula
    · exact nativeHeat092Fixed14_formula
    · exact nativeHeat092Fixed15_formula
    · exact nativeHeat092Fixed16_formula
    · exact nativeHeat092Fixed17_formula
    · exact nativeHeat092Fixed18_formula
    · exact nativeHeat092Fixed19_formula
    · exact nativeHeat092Fixed20_formula

theorem nativeHeatStep_chk_092_Gen :
    nativeHeatPassRootsOk nativeGap093Old nativeHeat092Frames nativeHeat092Coef nativeHeat092Fixed nativeHeat092Base 48 nativeHeat092Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_092_Gen : NativeHeatStepPassNum 92 := by
  refine nativeHeatStepPassNum_of_literals 92 nativeGap093Old nativeHeat092Frames (nativeHeatExpArg nativeGap093Old)
    nativeHeat092Exp nativeHeat092Coef nativeHeat092Fixed nativeHeat092Init nativeHeat092Base nativeHeatStep_hOld_092_Gen
    nativeHeatStep_hFr_092_Gen nativeHeatStep_hArg_092_Gen nativeHeatStep_hExp_092_Gen
    nativeHeatStep_hCoef_092_Gen nativeHeatStep_hFixed_092_Gen
    nativeHeatStep_hInit_092_Gen nativeHeatStep_hBase_092_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_092_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_092_Gen :
    nativeHeatY0Gen 92 = nativeShiftedFrame 1 (min nativeGap093Old.x nativeGap093Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_092_Gen, nativeHeatStep_hInd_092_Gen]

theorem nativeHeatStepFrameNum_092_Gen : NativeHeatStepFrameNum 92 := by
  have h1 := nativeHeatStep_hOld_092_Gen
  have h2 := nativeHeatStep_hInd_092_Gen
  have h3 := nativeHeatStep_hVar_092_Gen
  have h4 := nativeHeatStep_hQm_092_Gen
  have h5 := nativeHeatStep_hQN_092_Gen
  have h6 := nativeHeatStep_hY0_092_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_092_Gen : NativeHeatStepIndivNum 92 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 92 (by norm_num)) = nativeGap093Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_092_Gen]; exact nativeGap093Old_source
  · rw [hc, nativeHeatStep_hInd_092_Gen]; exact nativeGap093Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_092_Gen : nativeHeatY48Gen 92 = nativeHeat092Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_092_Gen, nativeHeatStep_hFr_092_Gen,
    nativeHeatStep_hCoef_092_Gen, nativeHeatStep_hFixed_092_Gen,
    nativeHeatStep_hBase_092_Gen]
  exact nativeHeat092All48

theorem nativeHeatResultGen_092 : nativeHeatResultGen 92 = nativeHeat092Result := by
  rw [← nativeHeat092Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_092_Gen, nativeHeatStep_hY0_092_Gen, nativeHeatStep_hExp_092_Gen,
    nativeHeatStep_hInit_092_Gen, nativeHeatStep_hFixed_092_Gen]

end ASDExplicitGamma.Native

end
