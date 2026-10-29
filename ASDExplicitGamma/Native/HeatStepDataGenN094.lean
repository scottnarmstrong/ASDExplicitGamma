module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat094Complete
public import ASDExplicitGamma.Numerics.Native.Gap095Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_094_Gen : nativeHeatOldRowGen 94 = nativeGap095Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_094_Gen : nativeHeatIndividualGen 94 = nativeGap095Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_094_Gen : nativeHeatGenVariance 94 = nativeHeat094Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_094_Gen, nativeHeat094Variance_formula]

theorem nativeHeatStep_hSpec_094_Gen : nativeHeatGenSpectral 94 = nativeHeat094Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_094_Gen, nativeHeat094Variance_formula]

theorem nativeHeatStep_hQm_094_Gen : nativeHeatGenQm 94 = nativeHeat094Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_094_Gen, nativeHeatStep_hSpec_094_Gen,
    nativeHeat094Qm_formula]

theorem nativeHeatStep_hQN_094_Gen : nativeHeatQNGen 94 = nativeHeat094QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_094_Gen, nativeHeat094QN_formula]

theorem nativeHeatStep_hFr_094_Gen : nativeHeatFramesGen 94 = nativeHeat094Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_094_Gen, nativeHeatStep_hInd_094_Gen,
    nativeHeatStep_hVar_094_Gen, nativeHeatStep_hQN_094_Gen, nativeHeat094Frames_formula]

theorem nativeHeatStep_hArg_094_Gen : nativeHeatExpArgGen 94 = nativeHeatExpArg nativeGap095Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_094_Gen]

theorem nativeHeatStep_hExp_094_Gen : nativeHeatExpGen 94 = nativeHeat094Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_094_Gen, nativeHeat094Exp_formula]

theorem nativeHeatStep_hCoef_094_Gen : nativeHeatCoefGen 94 = nativeHeat094Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_094_Gen, nativeHeat094Coef_formula]

theorem nativeHeatStep_hInit_094_Gen : nativeHeatInitGen 94 = nativeHeat094Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_094_Gen, nativeHeatStep_hVar_094_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat094Init00_formula
    · exact nativeHeat094Init01_formula
    · exact nativeHeat094Init02_formula
    · exact nativeHeat094Init03_formula
    · exact nativeHeat094Init04_formula
    · exact nativeHeat094Init05_formula
    · exact nativeHeat094Init06_formula
    · exact nativeHeat094Init07_formula
    · exact nativeHeat094Init08_formula
    · exact nativeHeat094Init09_formula
    · exact nativeHeat094Init10_formula
    · exact nativeHeat094Init11_formula
    · exact nativeHeat094Init12_formula
    · exact nativeHeat094Init13_formula
    · exact nativeHeat094Init14_formula
    · exact nativeHeat094Init15_formula
    · exact nativeHeat094Init16_formula
    · exact nativeHeat094Init17_formula
    · exact nativeHeat094Init18_formula
    · exact nativeHeat094Init19_formula
    · exact nativeHeat094Init20_formula
theorem nativeHeatStep_hBase_094_Gen : nativeHeatBaseGen 94 = nativeHeat094Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_094_Gen, nativeHeatStep_hInit_094_Gen, nativeHeat094Base_formula]

theorem nativeHeatStep_hFixed_094_Gen : nativeHeatFixedGen 94 = nativeHeat094Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_094_Gen, nativeHeatStep_hFr_094_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat094Fixed01_formula
    · exact nativeHeat094Fixed02_formula
    · exact nativeHeat094Fixed03_formula
    · exact nativeHeat094Fixed04_formula
    · exact nativeHeat094Fixed05_formula
    · exact nativeHeat094Fixed06_formula
    · exact nativeHeat094Fixed07_formula
    · exact nativeHeat094Fixed08_formula
    · exact nativeHeat094Fixed09_formula
    · exact nativeHeat094Fixed10_formula
    · exact nativeHeat094Fixed11_formula
    · exact nativeHeat094Fixed12_formula
    · exact nativeHeat094Fixed13_formula
    · exact nativeHeat094Fixed14_formula
    · exact nativeHeat094Fixed15_formula
    · exact nativeHeat094Fixed16_formula
    · exact nativeHeat094Fixed17_formula
    · exact nativeHeat094Fixed18_formula
    · exact nativeHeat094Fixed19_formula
    · exact nativeHeat094Fixed20_formula

theorem nativeHeatStep_chk_094_Gen :
    nativeHeatPassRootsOk nativeGap095Old nativeHeat094Frames nativeHeat094Coef nativeHeat094Fixed nativeHeat094Base 48 nativeHeat094Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_094_Gen : NativeHeatStepPassNum 94 := by
  refine nativeHeatStepPassNum_of_literals 94 nativeGap095Old nativeHeat094Frames (nativeHeatExpArg nativeGap095Old)
    nativeHeat094Exp nativeHeat094Coef nativeHeat094Fixed nativeHeat094Init nativeHeat094Base nativeHeatStep_hOld_094_Gen
    nativeHeatStep_hFr_094_Gen nativeHeatStep_hArg_094_Gen nativeHeatStep_hExp_094_Gen
    nativeHeatStep_hCoef_094_Gen nativeHeatStep_hFixed_094_Gen
    nativeHeatStep_hInit_094_Gen nativeHeatStep_hBase_094_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_094_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_094_Gen :
    nativeHeatY0Gen 94 = nativeShiftedFrame 1 (min nativeGap095Old.x nativeGap095Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_094_Gen, nativeHeatStep_hInd_094_Gen]

theorem nativeHeatStepFrameNum_094_Gen : NativeHeatStepFrameNum 94 := by
  have h1 := nativeHeatStep_hOld_094_Gen
  have h2 := nativeHeatStep_hInd_094_Gen
  have h3 := nativeHeatStep_hVar_094_Gen
  have h4 := nativeHeatStep_hQm_094_Gen
  have h5 := nativeHeatStep_hQN_094_Gen
  have h6 := nativeHeatStep_hY0_094_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_094_Gen : NativeHeatStepIndivNum 94 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 94 (by norm_num)) = nativeGap095Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_094_Gen]; exact nativeGap095Old_source
  · rw [hc, nativeHeatStep_hInd_094_Gen]; exact nativeGap095Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_094_Gen : nativeHeatY48Gen 94 = nativeHeat094Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_094_Gen, nativeHeatStep_hFr_094_Gen,
    nativeHeatStep_hCoef_094_Gen, nativeHeatStep_hFixed_094_Gen,
    nativeHeatStep_hBase_094_Gen]
  exact nativeHeat094All48

theorem nativeHeatResultGen_094 : nativeHeatResultGen 94 = nativeHeat094Result := by
  rw [← nativeHeat094Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_094_Gen, nativeHeatStep_hY0_094_Gen, nativeHeatStep_hExp_094_Gen,
    nativeHeatStep_hInit_094_Gen, nativeHeatStep_hFixed_094_Gen]

end ASDExplicitGamma.Native

end
