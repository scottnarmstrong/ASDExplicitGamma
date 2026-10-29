module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat042Complete
public import ASDExplicitGamma.Numerics.Native.Gap043Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_042_Gen : nativeHeatOldRowGen 42 = nativeGap043Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_042_Gen : nativeHeatIndividualGen 42 = nativeGap043Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_042_Gen : nativeHeatGenVariance 42 = nativeHeat042Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_042_Gen, nativeHeat042Variance_formula]

theorem nativeHeatStep_hSpec_042_Gen : nativeHeatGenSpectral 42 = nativeHeat042Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_042_Gen, nativeHeat042Variance_formula]

theorem nativeHeatStep_hQm_042_Gen : nativeHeatGenQm 42 = nativeHeat042Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_042_Gen, nativeHeatStep_hSpec_042_Gen,
    nativeHeat042Qm_formula]

theorem nativeHeatStep_hQN_042_Gen : nativeHeatQNGen 42 = nativeHeat042QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_042_Gen, nativeHeat042QN_formula]

theorem nativeHeatStep_hFr_042_Gen : nativeHeatFramesGen 42 = nativeHeat042Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_042_Gen, nativeHeatStep_hInd_042_Gen,
    nativeHeatStep_hVar_042_Gen, nativeHeatStep_hQN_042_Gen, nativeHeat042Frames_formula]

theorem nativeHeatStep_hArg_042_Gen : nativeHeatExpArgGen 42 = nativeHeatExpArg nativeGap043Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_042_Gen]

theorem nativeHeatStep_hExp_042_Gen : nativeHeatExpGen 42 = nativeHeat042Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_042_Gen, nativeHeat042Exp_formula]

theorem nativeHeatStep_hCoef_042_Gen : nativeHeatCoefGen 42 = nativeHeat042Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_042_Gen, nativeHeat042Coef_formula]

theorem nativeHeatStep_hInit_042_Gen : nativeHeatInitGen 42 = nativeHeat042Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_042_Gen, nativeHeatStep_hVar_042_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat042Init00_formula
    · exact nativeHeat042Init01_formula
    · exact nativeHeat042Init02_formula
    · exact nativeHeat042Init03_formula
    · exact nativeHeat042Init04_formula
    · exact nativeHeat042Init05_formula
    · exact nativeHeat042Init06_formula
    · exact nativeHeat042Init07_formula
    · exact nativeHeat042Init08_formula
    · exact nativeHeat042Init09_formula
    · exact nativeHeat042Init10_formula
    · exact nativeHeat042Init11_formula
    · exact nativeHeat042Init12_formula
    · exact nativeHeat042Init13_formula
    · exact nativeHeat042Init14_formula
    · exact nativeHeat042Init15_formula
    · exact nativeHeat042Init16_formula
    · exact nativeHeat042Init17_formula
    · exact nativeHeat042Init18_formula
    · exact nativeHeat042Init19_formula
    · exact nativeHeat042Init20_formula
theorem nativeHeatStep_hBase_042_Gen : nativeHeatBaseGen 42 = nativeHeat042Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_042_Gen, nativeHeatStep_hInit_042_Gen, nativeHeat042Base_formula]

theorem nativeHeatStep_hFixed_042_Gen : nativeHeatFixedGen 42 = nativeHeat042Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_042_Gen, nativeHeatStep_hFr_042_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat042Fixed01_formula
    · exact nativeHeat042Fixed02_formula
    · exact nativeHeat042Fixed03_formula
    · exact nativeHeat042Fixed04_formula
    · exact nativeHeat042Fixed05_formula
    · exact nativeHeat042Fixed06_formula
    · exact nativeHeat042Fixed07_formula
    · exact nativeHeat042Fixed08_formula
    · exact nativeHeat042Fixed09_formula
    · exact nativeHeat042Fixed10_formula
    · exact nativeHeat042Fixed11_formula
    · exact nativeHeat042Fixed12_formula
    · exact nativeHeat042Fixed13_formula
    · exact nativeHeat042Fixed14_formula
    · exact nativeHeat042Fixed15_formula
    · exact nativeHeat042Fixed16_formula
    · exact nativeHeat042Fixed17_formula
    · exact nativeHeat042Fixed18_formula
    · exact nativeHeat042Fixed19_formula
    · exact nativeHeat042Fixed20_formula

theorem nativeHeatStep_chk_042_Gen :
    nativeHeatPassRootsOk nativeGap043Old nativeHeat042Frames nativeHeat042Coef nativeHeat042Fixed nativeHeat042Base 48 nativeHeat042Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_042_Gen : NativeHeatStepPassNum 42 := by
  refine nativeHeatStepPassNum_of_literals 42 nativeGap043Old nativeHeat042Frames (nativeHeatExpArg nativeGap043Old)
    nativeHeat042Exp nativeHeat042Coef nativeHeat042Fixed nativeHeat042Init nativeHeat042Base nativeHeatStep_hOld_042_Gen
    nativeHeatStep_hFr_042_Gen nativeHeatStep_hArg_042_Gen nativeHeatStep_hExp_042_Gen
    nativeHeatStep_hCoef_042_Gen nativeHeatStep_hFixed_042_Gen
    nativeHeatStep_hInit_042_Gen nativeHeatStep_hBase_042_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_042_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_042_Gen :
    nativeHeatY0Gen 42 = nativeShiftedFrame 1 (min nativeGap043Old.x nativeGap043Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_042_Gen, nativeHeatStep_hInd_042_Gen]

theorem nativeHeatStepFrameNum_042_Gen : NativeHeatStepFrameNum 42 := by
  have h1 := nativeHeatStep_hOld_042_Gen
  have h2 := nativeHeatStep_hInd_042_Gen
  have h3 := nativeHeatStep_hVar_042_Gen
  have h4 := nativeHeatStep_hQm_042_Gen
  have h5 := nativeHeatStep_hQN_042_Gen
  have h6 := nativeHeatStep_hY0_042_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_042_Gen : NativeHeatStepIndivNum 42 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 42 (by norm_num)) = nativeGap043Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_042_Gen]; exact nativeGap043Old_source
  · rw [hc, nativeHeatStep_hInd_042_Gen]; exact nativeGap043Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_042_Gen : nativeHeatY48Gen 42 = nativeHeat042Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_042_Gen, nativeHeatStep_hFr_042_Gen,
    nativeHeatStep_hCoef_042_Gen, nativeHeatStep_hFixed_042_Gen,
    nativeHeatStep_hBase_042_Gen]
  exact nativeHeat042All48

theorem nativeHeatResultGen_042 : nativeHeatResultGen 42 = nativeHeat042Result := by
  rw [← nativeHeat042Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_042_Gen, nativeHeatStep_hY0_042_Gen, nativeHeatStep_hExp_042_Gen,
    nativeHeatStep_hInit_042_Gen, nativeHeatStep_hFixed_042_Gen]

end ASDExplicitGamma.Native

end
