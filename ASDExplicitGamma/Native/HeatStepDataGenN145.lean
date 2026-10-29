module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat145Complete
public import ASDExplicitGamma.Numerics.Native.Gap146Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_145_Gen : nativeHeatOldRowGen 145 = nativeGap146Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_145_Gen : nativeHeatIndividualGen 145 = nativeGap146Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_145_Gen : nativeHeatGenVariance 145 = nativeHeat145Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_145_Gen, nativeHeat145Variance_formula]

theorem nativeHeatStep_hSpec_145_Gen : nativeHeatGenSpectral 145 = nativeHeat145Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_145_Gen, nativeHeat145Variance_formula]

theorem nativeHeatStep_hQm_145_Gen : nativeHeatGenQm 145 = nativeHeat145Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_145_Gen, nativeHeatStep_hSpec_145_Gen,
    nativeHeat145Qm_formula]

theorem nativeHeatStep_hQN_145_Gen : nativeHeatQNGen 145 = nativeHeat145QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_145_Gen, nativeHeat145QN_formula]

theorem nativeHeatStep_hFr_145_Gen : nativeHeatFramesGen 145 = nativeHeat145Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_145_Gen, nativeHeatStep_hInd_145_Gen,
    nativeHeatStep_hVar_145_Gen, nativeHeatStep_hQN_145_Gen, nativeHeat145Frames_formula]

theorem nativeHeatStep_hArg_145_Gen : nativeHeatExpArgGen 145 = nativeHeatExpArg nativeGap146Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_145_Gen]

theorem nativeHeatStep_hExp_145_Gen : nativeHeatExpGen 145 = nativeHeat145Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_145_Gen, nativeHeat145Exp_formula]

theorem nativeHeatStep_hCoef_145_Gen : nativeHeatCoefGen 145 = nativeHeat145Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_145_Gen, nativeHeat145Coef_formula]

theorem nativeHeatStep_hInit_145_Gen : nativeHeatInitGen 145 = nativeHeat145Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_145_Gen, nativeHeatStep_hVar_145_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat145Init00_formula
    · exact nativeHeat145Init01_formula
    · exact nativeHeat145Init02_formula
    · exact nativeHeat145Init03_formula
    · exact nativeHeat145Init04_formula
    · exact nativeHeat145Init05_formula
    · exact nativeHeat145Init06_formula
    · exact nativeHeat145Init07_formula
    · exact nativeHeat145Init08_formula
    · exact nativeHeat145Init09_formula
    · exact nativeHeat145Init10_formula
    · exact nativeHeat145Init11_formula
    · exact nativeHeat145Init12_formula
    · exact nativeHeat145Init13_formula
    · exact nativeHeat145Init14_formula
    · exact nativeHeat145Init15_formula
    · exact nativeHeat145Init16_formula
    · exact nativeHeat145Init17_formula
    · exact nativeHeat145Init18_formula
    · exact nativeHeat145Init19_formula
    · exact nativeHeat145Init20_formula
theorem nativeHeatStep_hBase_145_Gen : nativeHeatBaseGen 145 = nativeHeat145Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_145_Gen, nativeHeatStep_hInit_145_Gen, nativeHeat145Base_formula]

theorem nativeHeatStep_hFixed_145_Gen : nativeHeatFixedGen 145 = nativeHeat145Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_145_Gen, nativeHeatStep_hFr_145_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat145Fixed01_formula
    · exact nativeHeat145Fixed02_formula
    · exact nativeHeat145Fixed03_formula
    · exact nativeHeat145Fixed04_formula
    · exact nativeHeat145Fixed05_formula
    · exact nativeHeat145Fixed06_formula
    · exact nativeHeat145Fixed07_formula
    · exact nativeHeat145Fixed08_formula
    · exact nativeHeat145Fixed09_formula
    · exact nativeHeat145Fixed10_formula
    · exact nativeHeat145Fixed11_formula
    · exact nativeHeat145Fixed12_formula
    · exact nativeHeat145Fixed13_formula
    · exact nativeHeat145Fixed14_formula
    · exact nativeHeat145Fixed15_formula
    · exact nativeHeat145Fixed16_formula
    · exact nativeHeat145Fixed17_formula
    · exact nativeHeat145Fixed18_formula
    · exact nativeHeat145Fixed19_formula
    · exact nativeHeat145Fixed20_formula

theorem nativeHeatStep_chk_145_Gen :
    nativeHeatPassRootsOk nativeGap146Old nativeHeat145Frames nativeHeat145Coef nativeHeat145Fixed nativeHeat145Base 48 nativeHeat145Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_145_Gen : NativeHeatStepPassNum 145 := by
  refine nativeHeatStepPassNum_of_literals 145 nativeGap146Old nativeHeat145Frames (nativeHeatExpArg nativeGap146Old)
    nativeHeat145Exp nativeHeat145Coef nativeHeat145Fixed nativeHeat145Init nativeHeat145Base nativeHeatStep_hOld_145_Gen
    nativeHeatStep_hFr_145_Gen nativeHeatStep_hArg_145_Gen nativeHeatStep_hExp_145_Gen
    nativeHeatStep_hCoef_145_Gen nativeHeatStep_hFixed_145_Gen
    nativeHeatStep_hInit_145_Gen nativeHeatStep_hBase_145_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_145_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_145_Gen :
    nativeHeatY0Gen 145 = nativeShiftedFrame 1 (min nativeGap146Old.x nativeGap146Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_145_Gen, nativeHeatStep_hInd_145_Gen]

theorem nativeHeatStepFrameNum_145_Gen : NativeHeatStepFrameNum 145 := by
  have h1 := nativeHeatStep_hOld_145_Gen
  have h2 := nativeHeatStep_hInd_145_Gen
  have h3 := nativeHeatStep_hVar_145_Gen
  have h4 := nativeHeatStep_hQm_145_Gen
  have h5 := nativeHeatStep_hQN_145_Gen
  have h6 := nativeHeatStep_hY0_145_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_145_Gen : NativeHeatStepIndivNum 145 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 145 (by norm_num)) = nativeGap146Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_145_Gen]; exact nativeGap146Old_source
  · rw [hc, nativeHeatStep_hInd_145_Gen]; exact nativeGap146Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_145_Gen : nativeHeatY48Gen 145 = nativeHeat145Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_145_Gen, nativeHeatStep_hFr_145_Gen,
    nativeHeatStep_hCoef_145_Gen, nativeHeatStep_hFixed_145_Gen,
    nativeHeatStep_hBase_145_Gen]
  exact nativeHeat145All48

theorem nativeHeatResultGen_145 : nativeHeatResultGen 145 = nativeHeat145Result := by
  rw [← nativeHeat145Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_145_Gen, nativeHeatStep_hY0_145_Gen, nativeHeatStep_hExp_145_Gen,
    nativeHeatStep_hInit_145_Gen, nativeHeatStep_hFixed_145_Gen]

end ASDExplicitGamma.Native

end
