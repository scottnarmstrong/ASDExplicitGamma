module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat093Complete
public import ASDExplicitGamma.Numerics.Native.Gap094Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_093_Gen : nativeHeatOldRowGen 93 = nativeGap094Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_093_Gen : nativeHeatIndividualGen 93 = nativeGap094Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_093_Gen : nativeHeatGenVariance 93 = nativeHeat093Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_093_Gen, nativeHeat093Variance_formula]

theorem nativeHeatStep_hSpec_093_Gen : nativeHeatGenSpectral 93 = nativeHeat093Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_093_Gen, nativeHeat093Variance_formula]

theorem nativeHeatStep_hQm_093_Gen : nativeHeatGenQm 93 = nativeHeat093Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_093_Gen, nativeHeatStep_hSpec_093_Gen,
    nativeHeat093Qm_formula]

theorem nativeHeatStep_hQN_093_Gen : nativeHeatQNGen 93 = nativeHeat093QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_093_Gen, nativeHeat093QN_formula]

theorem nativeHeatStep_hFr_093_Gen : nativeHeatFramesGen 93 = nativeHeat093Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_093_Gen, nativeHeatStep_hInd_093_Gen,
    nativeHeatStep_hVar_093_Gen, nativeHeatStep_hQN_093_Gen, nativeHeat093Frames_formula]

theorem nativeHeatStep_hArg_093_Gen : nativeHeatExpArgGen 93 = nativeHeatExpArg nativeGap094Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_093_Gen]

theorem nativeHeatStep_hExp_093_Gen : nativeHeatExpGen 93 = nativeHeat093Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_093_Gen, nativeHeat093Exp_formula]

theorem nativeHeatStep_hCoef_093_Gen : nativeHeatCoefGen 93 = nativeHeat093Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_093_Gen, nativeHeat093Coef_formula]

theorem nativeHeatStep_hInit_093_Gen : nativeHeatInitGen 93 = nativeHeat093Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_093_Gen, nativeHeatStep_hVar_093_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat093Init00_formula
    · exact nativeHeat093Init01_formula
    · exact nativeHeat093Init02_formula
    · exact nativeHeat093Init03_formula
    · exact nativeHeat093Init04_formula
    · exact nativeHeat093Init05_formula
    · exact nativeHeat093Init06_formula
    · exact nativeHeat093Init07_formula
    · exact nativeHeat093Init08_formula
    · exact nativeHeat093Init09_formula
    · exact nativeHeat093Init10_formula
    · exact nativeHeat093Init11_formula
    · exact nativeHeat093Init12_formula
    · exact nativeHeat093Init13_formula
    · exact nativeHeat093Init14_formula
    · exact nativeHeat093Init15_formula
    · exact nativeHeat093Init16_formula
    · exact nativeHeat093Init17_formula
    · exact nativeHeat093Init18_formula
    · exact nativeHeat093Init19_formula
    · exact nativeHeat093Init20_formula
theorem nativeHeatStep_hBase_093_Gen : nativeHeatBaseGen 93 = nativeHeat093Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_093_Gen, nativeHeatStep_hInit_093_Gen, nativeHeat093Base_formula]

theorem nativeHeatStep_hFixed_093_Gen : nativeHeatFixedGen 93 = nativeHeat093Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_093_Gen, nativeHeatStep_hFr_093_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat093Fixed01_formula
    · exact nativeHeat093Fixed02_formula
    · exact nativeHeat093Fixed03_formula
    · exact nativeHeat093Fixed04_formula
    · exact nativeHeat093Fixed05_formula
    · exact nativeHeat093Fixed06_formula
    · exact nativeHeat093Fixed07_formula
    · exact nativeHeat093Fixed08_formula
    · exact nativeHeat093Fixed09_formula
    · exact nativeHeat093Fixed10_formula
    · exact nativeHeat093Fixed11_formula
    · exact nativeHeat093Fixed12_formula
    · exact nativeHeat093Fixed13_formula
    · exact nativeHeat093Fixed14_formula
    · exact nativeHeat093Fixed15_formula
    · exact nativeHeat093Fixed16_formula
    · exact nativeHeat093Fixed17_formula
    · exact nativeHeat093Fixed18_formula
    · exact nativeHeat093Fixed19_formula
    · exact nativeHeat093Fixed20_formula

theorem nativeHeatStep_chk_093_Gen :
    nativeHeatPassRootsOk nativeGap094Old nativeHeat093Frames nativeHeat093Coef nativeHeat093Fixed nativeHeat093Base 48 nativeHeat093Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_093_Gen : NativeHeatStepPassNum 93 := by
  refine nativeHeatStepPassNum_of_literals 93 nativeGap094Old nativeHeat093Frames (nativeHeatExpArg nativeGap094Old)
    nativeHeat093Exp nativeHeat093Coef nativeHeat093Fixed nativeHeat093Init nativeHeat093Base nativeHeatStep_hOld_093_Gen
    nativeHeatStep_hFr_093_Gen nativeHeatStep_hArg_093_Gen nativeHeatStep_hExp_093_Gen
    nativeHeatStep_hCoef_093_Gen nativeHeatStep_hFixed_093_Gen
    nativeHeatStep_hInit_093_Gen nativeHeatStep_hBase_093_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_093_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_093_Gen :
    nativeHeatY0Gen 93 = nativeShiftedFrame 1 (min nativeGap094Old.x nativeGap094Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_093_Gen, nativeHeatStep_hInd_093_Gen]

theorem nativeHeatStepFrameNum_093_Gen : NativeHeatStepFrameNum 93 := by
  have h1 := nativeHeatStep_hOld_093_Gen
  have h2 := nativeHeatStep_hInd_093_Gen
  have h3 := nativeHeatStep_hVar_093_Gen
  have h4 := nativeHeatStep_hQm_093_Gen
  have h5 := nativeHeatStep_hQN_093_Gen
  have h6 := nativeHeatStep_hY0_093_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_093_Gen : NativeHeatStepIndivNum 93 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 93 (by norm_num)) = nativeGap094Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_093_Gen]; exact nativeGap094Old_source
  · rw [hc, nativeHeatStep_hInd_093_Gen]; exact nativeGap094Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_093_Gen : nativeHeatY48Gen 93 = nativeHeat093Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_093_Gen, nativeHeatStep_hFr_093_Gen,
    nativeHeatStep_hCoef_093_Gen, nativeHeatStep_hFixed_093_Gen,
    nativeHeatStep_hBase_093_Gen]
  exact nativeHeat093All48

theorem nativeHeatResultGen_093 : nativeHeatResultGen 93 = nativeHeat093Result := by
  rw [← nativeHeat093Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_093_Gen, nativeHeatStep_hY0_093_Gen, nativeHeatStep_hExp_093_Gen,
    nativeHeatStep_hInit_093_Gen, nativeHeatStep_hFixed_093_Gen]

end ASDExplicitGamma.Native

end
