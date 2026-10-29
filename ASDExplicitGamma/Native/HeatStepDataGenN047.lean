module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat047Complete
public import ASDExplicitGamma.Numerics.Native.Gap048Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_047_Gen : nativeHeatOldRowGen 47 = nativeGap048Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_047_Gen : nativeHeatIndividualGen 47 = nativeGap048Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_047_Gen : nativeHeatGenVariance 47 = nativeHeat047Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_047_Gen, nativeHeat047Variance_formula]

theorem nativeHeatStep_hSpec_047_Gen : nativeHeatGenSpectral 47 = nativeHeat047Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_047_Gen, nativeHeat047Variance_formula]

theorem nativeHeatStep_hQm_047_Gen : nativeHeatGenQm 47 = nativeHeat047Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_047_Gen, nativeHeatStep_hSpec_047_Gen,
    nativeHeat047Qm_formula]

theorem nativeHeatStep_hQN_047_Gen : nativeHeatQNGen 47 = nativeHeat047QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_047_Gen, nativeHeat047QN_formula]

theorem nativeHeatStep_hFr_047_Gen : nativeHeatFramesGen 47 = nativeHeat047Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_047_Gen, nativeHeatStep_hInd_047_Gen,
    nativeHeatStep_hVar_047_Gen, nativeHeatStep_hQN_047_Gen, nativeHeat047Frames_formula]

theorem nativeHeatStep_hArg_047_Gen : nativeHeatExpArgGen 47 = nativeHeatExpArg nativeGap048Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_047_Gen]

theorem nativeHeatStep_hExp_047_Gen : nativeHeatExpGen 47 = nativeHeat047Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_047_Gen, nativeHeat047Exp_formula]

theorem nativeHeatStep_hCoef_047_Gen : nativeHeatCoefGen 47 = nativeHeat047Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_047_Gen, nativeHeat047Coef_formula]

theorem nativeHeatStep_hInit_047_Gen : nativeHeatInitGen 47 = nativeHeat047Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_047_Gen, nativeHeatStep_hVar_047_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat047Init00_formula
    · exact nativeHeat047Init01_formula
    · exact nativeHeat047Init02_formula
    · exact nativeHeat047Init03_formula
    · exact nativeHeat047Init04_formula
    · exact nativeHeat047Init05_formula
    · exact nativeHeat047Init06_formula
    · exact nativeHeat047Init07_formula
    · exact nativeHeat047Init08_formula
    · exact nativeHeat047Init09_formula
    · exact nativeHeat047Init10_formula
    · exact nativeHeat047Init11_formula
    · exact nativeHeat047Init12_formula
    · exact nativeHeat047Init13_formula
    · exact nativeHeat047Init14_formula
    · exact nativeHeat047Init15_formula
    · exact nativeHeat047Init16_formula
    · exact nativeHeat047Init17_formula
    · exact nativeHeat047Init18_formula
    · exact nativeHeat047Init19_formula
    · exact nativeHeat047Init20_formula
theorem nativeHeatStep_hBase_047_Gen : nativeHeatBaseGen 47 = nativeHeat047Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_047_Gen, nativeHeatStep_hInit_047_Gen, nativeHeat047Base_formula]

theorem nativeHeatStep_hFixed_047_Gen : nativeHeatFixedGen 47 = nativeHeat047Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_047_Gen, nativeHeatStep_hFr_047_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat047Fixed01_formula
    · exact nativeHeat047Fixed02_formula
    · exact nativeHeat047Fixed03_formula
    · exact nativeHeat047Fixed04_formula
    · exact nativeHeat047Fixed05_formula
    · exact nativeHeat047Fixed06_formula
    · exact nativeHeat047Fixed07_formula
    · exact nativeHeat047Fixed08_formula
    · exact nativeHeat047Fixed09_formula
    · exact nativeHeat047Fixed10_formula
    · exact nativeHeat047Fixed11_formula
    · exact nativeHeat047Fixed12_formula
    · exact nativeHeat047Fixed13_formula
    · exact nativeHeat047Fixed14_formula
    · exact nativeHeat047Fixed15_formula
    · exact nativeHeat047Fixed16_formula
    · exact nativeHeat047Fixed17_formula
    · exact nativeHeat047Fixed18_formula
    · exact nativeHeat047Fixed19_formula
    · exact nativeHeat047Fixed20_formula

theorem nativeHeatStep_chk_047_Gen :
    nativeHeatPassRootsOk nativeGap048Old nativeHeat047Frames nativeHeat047Coef nativeHeat047Fixed nativeHeat047Base 48 nativeHeat047Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_047_Gen : NativeHeatStepPassNum 47 := by
  refine nativeHeatStepPassNum_of_literals 47 nativeGap048Old nativeHeat047Frames (nativeHeatExpArg nativeGap048Old)
    nativeHeat047Exp nativeHeat047Coef nativeHeat047Fixed nativeHeat047Init nativeHeat047Base nativeHeatStep_hOld_047_Gen
    nativeHeatStep_hFr_047_Gen nativeHeatStep_hArg_047_Gen nativeHeatStep_hExp_047_Gen
    nativeHeatStep_hCoef_047_Gen nativeHeatStep_hFixed_047_Gen
    nativeHeatStep_hInit_047_Gen nativeHeatStep_hBase_047_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_047_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_047_Gen :
    nativeHeatY0Gen 47 = nativeShiftedFrame 1 (min nativeGap048Old.x nativeGap048Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_047_Gen, nativeHeatStep_hInd_047_Gen]

theorem nativeHeatStepFrameNum_047_Gen : NativeHeatStepFrameNum 47 := by
  have h1 := nativeHeatStep_hOld_047_Gen
  have h2 := nativeHeatStep_hInd_047_Gen
  have h3 := nativeHeatStep_hVar_047_Gen
  have h4 := nativeHeatStep_hQm_047_Gen
  have h5 := nativeHeatStep_hQN_047_Gen
  have h6 := nativeHeatStep_hY0_047_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_047_Gen : NativeHeatStepIndivNum 47 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 47 (by norm_num)) = nativeGap048Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_047_Gen]; exact nativeGap048Old_source
  · rw [hc, nativeHeatStep_hInd_047_Gen]; exact nativeGap048Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_047_Gen : nativeHeatY48Gen 47 = nativeHeat047Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_047_Gen, nativeHeatStep_hFr_047_Gen,
    nativeHeatStep_hCoef_047_Gen, nativeHeatStep_hFixed_047_Gen,
    nativeHeatStep_hBase_047_Gen]
  exact nativeHeat047All48

theorem nativeHeatResultGen_047 : nativeHeatResultGen 47 = nativeHeat047Result := by
  rw [← nativeHeat047Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_047_Gen, nativeHeatStep_hY0_047_Gen, nativeHeatStep_hExp_047_Gen,
    nativeHeatStep_hInit_047_Gen, nativeHeatStep_hFixed_047_Gen]

end ASDExplicitGamma.Native

end
