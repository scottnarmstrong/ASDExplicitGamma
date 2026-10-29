module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat069Complete
public import ASDExplicitGamma.Numerics.Native.Gap070Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_069_Gen : nativeHeatOldRowGen 69 = nativeGap070Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_069_Gen : nativeHeatIndividualGen 69 = nativeGap070Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_069_Gen : nativeHeatGenVariance 69 = nativeHeat069Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_069_Gen, nativeHeat069Variance_formula]

theorem nativeHeatStep_hSpec_069_Gen : nativeHeatGenSpectral 69 = nativeHeat069Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_069_Gen, nativeHeat069Variance_formula]

theorem nativeHeatStep_hQm_069_Gen : nativeHeatGenQm 69 = nativeHeat069Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_069_Gen, nativeHeatStep_hSpec_069_Gen,
    nativeHeat069Qm_formula]

theorem nativeHeatStep_hQN_069_Gen : nativeHeatQNGen 69 = nativeHeat069QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_069_Gen, nativeHeat069QN_formula]

theorem nativeHeatStep_hFr_069_Gen : nativeHeatFramesGen 69 = nativeHeat069Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_069_Gen, nativeHeatStep_hInd_069_Gen,
    nativeHeatStep_hVar_069_Gen, nativeHeatStep_hQN_069_Gen, nativeHeat069Frames_formula]

theorem nativeHeatStep_hArg_069_Gen : nativeHeatExpArgGen 69 = nativeHeatExpArg nativeGap070Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_069_Gen]

theorem nativeHeatStep_hExp_069_Gen : nativeHeatExpGen 69 = nativeHeat069Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_069_Gen, nativeHeat069Exp_formula]

theorem nativeHeatStep_hCoef_069_Gen : nativeHeatCoefGen 69 = nativeHeat069Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_069_Gen, nativeHeat069Coef_formula]

theorem nativeHeatStep_hInit_069_Gen : nativeHeatInitGen 69 = nativeHeat069Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_069_Gen, nativeHeatStep_hVar_069_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat069Init00_formula
    · exact nativeHeat069Init01_formula
    · exact nativeHeat069Init02_formula
    · exact nativeHeat069Init03_formula
    · exact nativeHeat069Init04_formula
    · exact nativeHeat069Init05_formula
    · exact nativeHeat069Init06_formula
    · exact nativeHeat069Init07_formula
    · exact nativeHeat069Init08_formula
    · exact nativeHeat069Init09_formula
    · exact nativeHeat069Init10_formula
    · exact nativeHeat069Init11_formula
    · exact nativeHeat069Init12_formula
    · exact nativeHeat069Init13_formula
    · exact nativeHeat069Init14_formula
    · exact nativeHeat069Init15_formula
    · exact nativeHeat069Init16_formula
    · exact nativeHeat069Init17_formula
    · exact nativeHeat069Init18_formula
    · exact nativeHeat069Init19_formula
    · exact nativeHeat069Init20_formula
theorem nativeHeatStep_hBase_069_Gen : nativeHeatBaseGen 69 = nativeHeat069Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_069_Gen, nativeHeatStep_hInit_069_Gen, nativeHeat069Base_formula]

theorem nativeHeatStep_hFixed_069_Gen : nativeHeatFixedGen 69 = nativeHeat069Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_069_Gen, nativeHeatStep_hFr_069_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat069Fixed01_formula
    · exact nativeHeat069Fixed02_formula
    · exact nativeHeat069Fixed03_formula
    · exact nativeHeat069Fixed04_formula
    · exact nativeHeat069Fixed05_formula
    · exact nativeHeat069Fixed06_formula
    · exact nativeHeat069Fixed07_formula
    · exact nativeHeat069Fixed08_formula
    · exact nativeHeat069Fixed09_formula
    · exact nativeHeat069Fixed10_formula
    · exact nativeHeat069Fixed11_formula
    · exact nativeHeat069Fixed12_formula
    · exact nativeHeat069Fixed13_formula
    · exact nativeHeat069Fixed14_formula
    · exact nativeHeat069Fixed15_formula
    · exact nativeHeat069Fixed16_formula
    · exact nativeHeat069Fixed17_formula
    · exact nativeHeat069Fixed18_formula
    · exact nativeHeat069Fixed19_formula
    · exact nativeHeat069Fixed20_formula

theorem nativeHeatStep_chk_069_Gen :
    nativeHeatPassRootsOk nativeGap070Old nativeHeat069Frames nativeHeat069Coef nativeHeat069Fixed nativeHeat069Base 48 nativeHeat069Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_069_Gen : NativeHeatStepPassNum 69 := by
  refine nativeHeatStepPassNum_of_literals 69 nativeGap070Old nativeHeat069Frames (nativeHeatExpArg nativeGap070Old)
    nativeHeat069Exp nativeHeat069Coef nativeHeat069Fixed nativeHeat069Init nativeHeat069Base nativeHeatStep_hOld_069_Gen
    nativeHeatStep_hFr_069_Gen nativeHeatStep_hArg_069_Gen nativeHeatStep_hExp_069_Gen
    nativeHeatStep_hCoef_069_Gen nativeHeatStep_hFixed_069_Gen
    nativeHeatStep_hInit_069_Gen nativeHeatStep_hBase_069_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_069_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_069_Gen :
    nativeHeatY0Gen 69 = nativeShiftedFrame 1 (min nativeGap070Old.x nativeGap070Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_069_Gen, nativeHeatStep_hInd_069_Gen]

theorem nativeHeatStepFrameNum_069_Gen : NativeHeatStepFrameNum 69 := by
  have h1 := nativeHeatStep_hOld_069_Gen
  have h2 := nativeHeatStep_hInd_069_Gen
  have h3 := nativeHeatStep_hVar_069_Gen
  have h4 := nativeHeatStep_hQm_069_Gen
  have h5 := nativeHeatStep_hQN_069_Gen
  have h6 := nativeHeatStep_hY0_069_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_069_Gen : NativeHeatStepIndivNum 69 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 69 (by norm_num)) = nativeGap070Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_069_Gen]; exact nativeGap070Old_source
  · rw [hc, nativeHeatStep_hInd_069_Gen]; exact nativeGap070Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_069_Gen : nativeHeatY48Gen 69 = nativeHeat069Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_069_Gen, nativeHeatStep_hFr_069_Gen,
    nativeHeatStep_hCoef_069_Gen, nativeHeatStep_hFixed_069_Gen,
    nativeHeatStep_hBase_069_Gen]
  exact nativeHeat069All48

theorem nativeHeatResultGen_069 : nativeHeatResultGen 69 = nativeHeat069Result := by
  rw [← nativeHeat069Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_069_Gen, nativeHeatStep_hY0_069_Gen, nativeHeatStep_hExp_069_Gen,
    nativeHeatStep_hInit_069_Gen, nativeHeatStep_hFixed_069_Gen]

end ASDExplicitGamma.Native

end
