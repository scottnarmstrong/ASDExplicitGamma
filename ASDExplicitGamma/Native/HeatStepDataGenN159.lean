module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat159Complete
public import ASDExplicitGamma.Numerics.Native.Gap160Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_159_Gen : nativeHeatOldRowGen 159 = nativeGap160Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_159_Gen : nativeHeatIndividualGen 159 = nativeGap160Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_159_Gen : nativeHeatGenVariance 159 = nativeHeat159Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_159_Gen, nativeHeat159Variance_formula]

theorem nativeHeatStep_hSpec_159_Gen : nativeHeatGenSpectral 159 = nativeHeat159Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_159_Gen, nativeHeat159Variance_formula]

theorem nativeHeatStep_hQm_159_Gen : nativeHeatGenQm 159 = nativeHeat159Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_159_Gen, nativeHeatStep_hSpec_159_Gen,
    nativeHeat159Qm_formula]

theorem nativeHeatStep_hQN_159_Gen : nativeHeatQNGen 159 = nativeHeat159QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_159_Gen, nativeHeat159QN_formula]

theorem nativeHeatStep_hFr_159_Gen : nativeHeatFramesGen 159 = nativeHeat159Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_159_Gen, nativeHeatStep_hInd_159_Gen,
    nativeHeatStep_hVar_159_Gen, nativeHeatStep_hQN_159_Gen, nativeHeat159Frames_formula]

theorem nativeHeatStep_hArg_159_Gen : nativeHeatExpArgGen 159 = nativeHeatExpArg nativeGap160Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_159_Gen]

theorem nativeHeatStep_hExp_159_Gen : nativeHeatExpGen 159 = nativeHeat159Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_159_Gen, nativeHeat159Exp_formula]

theorem nativeHeatStep_hCoef_159_Gen : nativeHeatCoefGen 159 = nativeHeat159Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_159_Gen, nativeHeat159Coef_formula]

theorem nativeHeatStep_hInit_159_Gen : nativeHeatInitGen 159 = nativeHeat159Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_159_Gen, nativeHeatStep_hVar_159_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat159Init00_formula
    · exact nativeHeat159Init01_formula
    · exact nativeHeat159Init02_formula
    · exact nativeHeat159Init03_formula
    · exact nativeHeat159Init04_formula
    · exact nativeHeat159Init05_formula
    · exact nativeHeat159Init06_formula
    · exact nativeHeat159Init07_formula
    · exact nativeHeat159Init08_formula
    · exact nativeHeat159Init09_formula
    · exact nativeHeat159Init10_formula
    · exact nativeHeat159Init11_formula
    · exact nativeHeat159Init12_formula
    · exact nativeHeat159Init13_formula
    · exact nativeHeat159Init14_formula
    · exact nativeHeat159Init15_formula
    · exact nativeHeat159Init16_formula
    · exact nativeHeat159Init17_formula
    · exact nativeHeat159Init18_formula
    · exact nativeHeat159Init19_formula
    · exact nativeHeat159Init20_formula
theorem nativeHeatStep_hBase_159_Gen : nativeHeatBaseGen 159 = nativeHeat159Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_159_Gen, nativeHeatStep_hInit_159_Gen, nativeHeat159Base_formula]

theorem nativeHeatStep_hFixed_159_Gen : nativeHeatFixedGen 159 = nativeHeat159Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_159_Gen, nativeHeatStep_hFr_159_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat159Fixed01_formula
    · exact nativeHeat159Fixed02_formula
    · exact nativeHeat159Fixed03_formula
    · exact nativeHeat159Fixed04_formula
    · exact nativeHeat159Fixed05_formula
    · exact nativeHeat159Fixed06_formula
    · exact nativeHeat159Fixed07_formula
    · exact nativeHeat159Fixed08_formula
    · exact nativeHeat159Fixed09_formula
    · exact nativeHeat159Fixed10_formula
    · exact nativeHeat159Fixed11_formula
    · exact nativeHeat159Fixed12_formula
    · exact nativeHeat159Fixed13_formula
    · exact nativeHeat159Fixed14_formula
    · exact nativeHeat159Fixed15_formula
    · exact nativeHeat159Fixed16_formula
    · exact nativeHeat159Fixed17_formula
    · exact nativeHeat159Fixed18_formula
    · exact nativeHeat159Fixed19_formula
    · exact nativeHeat159Fixed20_formula

theorem nativeHeatStep_chk_159_Gen :
    nativeHeatPassRootsOk nativeGap160Old nativeHeat159Frames nativeHeat159Coef nativeHeat159Fixed nativeHeat159Base 48 nativeHeat159Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_159_Gen : NativeHeatStepPassNum 159 := by
  refine nativeHeatStepPassNum_of_literals 159 nativeGap160Old nativeHeat159Frames (nativeHeatExpArg nativeGap160Old)
    nativeHeat159Exp nativeHeat159Coef nativeHeat159Fixed nativeHeat159Init nativeHeat159Base nativeHeatStep_hOld_159_Gen
    nativeHeatStep_hFr_159_Gen nativeHeatStep_hArg_159_Gen nativeHeatStep_hExp_159_Gen
    nativeHeatStep_hCoef_159_Gen nativeHeatStep_hFixed_159_Gen
    nativeHeatStep_hInit_159_Gen nativeHeatStep_hBase_159_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_159_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_159_Gen :
    nativeHeatY0Gen 159 = nativeShiftedFrame 1 (min nativeGap160Old.x nativeGap160Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_159_Gen, nativeHeatStep_hInd_159_Gen]

theorem nativeHeatStepFrameNum_159_Gen : NativeHeatStepFrameNum 159 := by
  have h1 := nativeHeatStep_hOld_159_Gen
  have h2 := nativeHeatStep_hInd_159_Gen
  have h3 := nativeHeatStep_hVar_159_Gen
  have h4 := nativeHeatStep_hQm_159_Gen
  have h5 := nativeHeatStep_hQN_159_Gen
  have h6 := nativeHeatStep_hY0_159_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_159_Gen : NativeHeatStepIndivNum 159 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 159 (by norm_num)) = nativeGap160Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_159_Gen]; exact nativeGap160Old_source
  · rw [hc, nativeHeatStep_hInd_159_Gen]; exact nativeGap160Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_159_Gen : nativeHeatY48Gen 159 = nativeHeat159Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_159_Gen, nativeHeatStep_hFr_159_Gen,
    nativeHeatStep_hCoef_159_Gen, nativeHeatStep_hFixed_159_Gen,
    nativeHeatStep_hBase_159_Gen]
  exact nativeHeat159All48

theorem nativeHeatResultGen_159 : nativeHeatResultGen 159 = nativeHeat159Result := by
  rw [← nativeHeat159Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_159_Gen, nativeHeatStep_hY0_159_Gen, nativeHeatStep_hExp_159_Gen,
    nativeHeatStep_hInit_159_Gen, nativeHeatStep_hFixed_159_Gen]

end ASDExplicitGamma.Native

end
