module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat038Complete
public import ASDExplicitGamma.Numerics.Native.Gap039Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_038_Gen : nativeHeatOldRowGen 38 = nativeGap039Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_038_Gen : nativeHeatIndividualGen 38 = nativeGap039Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_038_Gen : nativeHeatGenVariance 38 = nativeHeat038Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_038_Gen, nativeHeat038Variance_formula]

theorem nativeHeatStep_hSpec_038_Gen : nativeHeatGenSpectral 38 = nativeHeat038Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_038_Gen, nativeHeat038Variance_formula]

theorem nativeHeatStep_hQm_038_Gen : nativeHeatGenQm 38 = nativeHeat038Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_038_Gen, nativeHeatStep_hSpec_038_Gen,
    nativeHeat038Qm_formula]

theorem nativeHeatStep_hQN_038_Gen : nativeHeatQNGen 38 = nativeHeat038QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_038_Gen, nativeHeat038QN_formula]

theorem nativeHeatStep_hFr_038_Gen : nativeHeatFramesGen 38 = nativeHeat038Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_038_Gen, nativeHeatStep_hInd_038_Gen,
    nativeHeatStep_hVar_038_Gen, nativeHeatStep_hQN_038_Gen, nativeHeat038Frames_formula]

theorem nativeHeatStep_hArg_038_Gen : nativeHeatExpArgGen 38 = nativeHeatExpArg nativeGap039Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_038_Gen]

theorem nativeHeatStep_hExp_038_Gen : nativeHeatExpGen 38 = nativeHeat038Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_038_Gen, nativeHeat038Exp_formula]

theorem nativeHeatStep_hCoef_038_Gen : nativeHeatCoefGen 38 = nativeHeat038Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_038_Gen, nativeHeat038Coef_formula]

theorem nativeHeatStep_hInit_038_Gen : nativeHeatInitGen 38 = nativeHeat038Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_038_Gen, nativeHeatStep_hVar_038_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat038Init00_formula
    · exact nativeHeat038Init01_formula
    · exact nativeHeat038Init02_formula
    · exact nativeHeat038Init03_formula
    · exact nativeHeat038Init04_formula
    · exact nativeHeat038Init05_formula
    · exact nativeHeat038Init06_formula
    · exact nativeHeat038Init07_formula
    · exact nativeHeat038Init08_formula
    · exact nativeHeat038Init09_formula
    · exact nativeHeat038Init10_formula
    · exact nativeHeat038Init11_formula
    · exact nativeHeat038Init12_formula
    · exact nativeHeat038Init13_formula
    · exact nativeHeat038Init14_formula
    · exact nativeHeat038Init15_formula
    · exact nativeHeat038Init16_formula
    · exact nativeHeat038Init17_formula
    · exact nativeHeat038Init18_formula
    · exact nativeHeat038Init19_formula
    · exact nativeHeat038Init20_formula
theorem nativeHeatStep_hBase_038_Gen : nativeHeatBaseGen 38 = nativeHeat038Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_038_Gen, nativeHeatStep_hInit_038_Gen, nativeHeat038Base_formula]

theorem nativeHeatStep_hFixed_038_Gen : nativeHeatFixedGen 38 = nativeHeat038Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_038_Gen, nativeHeatStep_hFr_038_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat038Fixed01_formula
    · exact nativeHeat038Fixed02_formula
    · exact nativeHeat038Fixed03_formula
    · exact nativeHeat038Fixed04_formula
    · exact nativeHeat038Fixed05_formula
    · exact nativeHeat038Fixed06_formula
    · exact nativeHeat038Fixed07_formula
    · exact nativeHeat038Fixed08_formula
    · exact nativeHeat038Fixed09_formula
    · exact nativeHeat038Fixed10_formula
    · exact nativeHeat038Fixed11_formula
    · exact nativeHeat038Fixed12_formula
    · exact nativeHeat038Fixed13_formula
    · exact nativeHeat038Fixed14_formula
    · exact nativeHeat038Fixed15_formula
    · exact nativeHeat038Fixed16_formula
    · exact nativeHeat038Fixed17_formula
    · exact nativeHeat038Fixed18_formula
    · exact nativeHeat038Fixed19_formula
    · exact nativeHeat038Fixed20_formula

theorem nativeHeatStep_chk_038_Gen :
    nativeHeatPassRootsOk nativeGap039Old nativeHeat038Frames nativeHeat038Coef nativeHeat038Fixed nativeHeat038Base 48 nativeHeat038Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_038_Gen : NativeHeatStepPassNum 38 := by
  refine nativeHeatStepPassNum_of_literals 38 nativeGap039Old nativeHeat038Frames (nativeHeatExpArg nativeGap039Old)
    nativeHeat038Exp nativeHeat038Coef nativeHeat038Fixed nativeHeat038Init nativeHeat038Base nativeHeatStep_hOld_038_Gen
    nativeHeatStep_hFr_038_Gen nativeHeatStep_hArg_038_Gen nativeHeatStep_hExp_038_Gen
    nativeHeatStep_hCoef_038_Gen nativeHeatStep_hFixed_038_Gen
    nativeHeatStep_hInit_038_Gen nativeHeatStep_hBase_038_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_038_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_038_Gen :
    nativeHeatY0Gen 38 = nativeShiftedFrame 1 (min nativeGap039Old.x nativeGap039Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_038_Gen, nativeHeatStep_hInd_038_Gen]

theorem nativeHeatStepFrameNum_038_Gen : NativeHeatStepFrameNum 38 := by
  have h1 := nativeHeatStep_hOld_038_Gen
  have h2 := nativeHeatStep_hInd_038_Gen
  have h3 := nativeHeatStep_hVar_038_Gen
  have h4 := nativeHeatStep_hQm_038_Gen
  have h5 := nativeHeatStep_hQN_038_Gen
  have h6 := nativeHeatStep_hY0_038_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_038_Gen : NativeHeatStepIndivNum 38 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 38 (by norm_num)) = nativeGap039Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_038_Gen]; exact nativeGap039Old_source
  · rw [hc, nativeHeatStep_hInd_038_Gen]; exact nativeGap039Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_038_Gen : nativeHeatY48Gen 38 = nativeHeat038Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_038_Gen, nativeHeatStep_hFr_038_Gen,
    nativeHeatStep_hCoef_038_Gen, nativeHeatStep_hFixed_038_Gen,
    nativeHeatStep_hBase_038_Gen]
  exact nativeHeat038All48

theorem nativeHeatResultGen_038 : nativeHeatResultGen 38 = nativeHeat038Result := by
  rw [← nativeHeat038Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_038_Gen, nativeHeatStep_hY0_038_Gen, nativeHeatStep_hExp_038_Gen,
    nativeHeatStep_hInit_038_Gen, nativeHeatStep_hFixed_038_Gen]

end ASDExplicitGamma.Native

end
