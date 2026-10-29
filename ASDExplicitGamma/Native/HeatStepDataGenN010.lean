module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat010Complete
public import ASDExplicitGamma.Numerics.Native.Gap011Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_010_Gen : nativeHeatOldRowGen 10 = nativeGap011Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_010_Gen : nativeHeatIndividualGen 10 = nativeGap011Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_010_Gen : nativeHeatGenVariance 10 = nativeHeat010Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_010_Gen, nativeHeat010Variance_formula]

theorem nativeHeatStep_hSpec_010_Gen : nativeHeatGenSpectral 10 = nativeHeat010Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_010_Gen, nativeHeat010Variance_formula]

theorem nativeHeatStep_hQm_010_Gen : nativeHeatGenQm 10 = nativeHeat010Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_010_Gen, nativeHeatStep_hSpec_010_Gen,
    nativeHeat010Qm_formula]

theorem nativeHeatStep_hQN_010_Gen : nativeHeatQNGen 10 = nativeHeat010QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_010_Gen, nativeHeat010QN_formula]

theorem nativeHeatStep_hFr_010_Gen : nativeHeatFramesGen 10 = nativeHeat010Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_010_Gen, nativeHeatStep_hInd_010_Gen,
    nativeHeatStep_hVar_010_Gen, nativeHeatStep_hQN_010_Gen, nativeHeat010Frames_formula]

theorem nativeHeatStep_hArg_010_Gen : nativeHeatExpArgGen 10 = nativeHeatExpArg nativeGap011Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_010_Gen]

theorem nativeHeatStep_hExp_010_Gen : nativeHeatExpGen 10 = nativeHeat010Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_010_Gen, nativeHeat010Exp_formula]

theorem nativeHeatStep_hCoef_010_Gen : nativeHeatCoefGen 10 = nativeHeat010Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_010_Gen, nativeHeat010Coef_formula]

theorem nativeHeatStep_hInit_010_Gen : nativeHeatInitGen 10 = nativeHeat010Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_010_Gen, nativeHeatStep_hVar_010_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat010Init00_formula
    · exact nativeHeat010Init01_formula
    · exact nativeHeat010Init02_formula
    · exact nativeHeat010Init03_formula
    · exact nativeHeat010Init04_formula
    · exact nativeHeat010Init05_formula
    · exact nativeHeat010Init06_formula
    · exact nativeHeat010Init07_formula
    · exact nativeHeat010Init08_formula
    · exact nativeHeat010Init09_formula
    · exact nativeHeat010Init10_formula
    · exact nativeHeat010Init11_formula
    · exact nativeHeat010Init12_formula
    · exact nativeHeat010Init13_formula
    · exact nativeHeat010Init14_formula
    · exact nativeHeat010Init15_formula
    · exact nativeHeat010Init16_formula
    · exact nativeHeat010Init17_formula
    · exact nativeHeat010Init18_formula
    · exact nativeHeat010Init19_formula
    · exact nativeHeat010Init20_formula
theorem nativeHeatStep_hBase_010_Gen : nativeHeatBaseGen 10 = nativeHeat010Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_010_Gen, nativeHeatStep_hInit_010_Gen, nativeHeat010Base_formula]

theorem nativeHeatStep_hFixed_010_Gen : nativeHeatFixedGen 10 = nativeHeat010Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_010_Gen, nativeHeatStep_hFr_010_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat010Fixed01_formula
    · exact nativeHeat010Fixed02_formula
    · exact nativeHeat010Fixed03_formula
    · exact nativeHeat010Fixed04_formula
    · exact nativeHeat010Fixed05_formula
    · exact nativeHeat010Fixed06_formula
    · exact nativeHeat010Fixed07_formula
    · exact nativeHeat010Fixed08_formula
    · exact nativeHeat010Fixed09_formula
    · exact nativeHeat010Fixed10_formula
    · exact nativeHeat010Fixed11_formula
    · exact nativeHeat010Fixed12_formula
    · exact nativeHeat010Fixed13_formula
    · exact nativeHeat010Fixed14_formula
    · exact nativeHeat010Fixed15_formula
    · exact nativeHeat010Fixed16_formula
    · exact nativeHeat010Fixed17_formula
    · exact nativeHeat010Fixed18_formula
    · exact nativeHeat010Fixed19_formula
    · exact nativeHeat010Fixed20_formula

theorem nativeHeatStep_chk_010_Gen :
    nativeHeatPassRootsOk nativeGap011Old nativeHeat010Frames nativeHeat010Coef nativeHeat010Fixed nativeHeat010Base 48 nativeHeat010Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_010_Gen : NativeHeatStepPassNum 10 := by
  refine nativeHeatStepPassNum_of_literals 10 nativeGap011Old nativeHeat010Frames (nativeHeatExpArg nativeGap011Old)
    nativeHeat010Exp nativeHeat010Coef nativeHeat010Fixed nativeHeat010Init nativeHeat010Base nativeHeatStep_hOld_010_Gen
    nativeHeatStep_hFr_010_Gen nativeHeatStep_hArg_010_Gen nativeHeatStep_hExp_010_Gen
    nativeHeatStep_hCoef_010_Gen nativeHeatStep_hFixed_010_Gen
    nativeHeatStep_hInit_010_Gen nativeHeatStep_hBase_010_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_010_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_010_Gen :
    nativeHeatY0Gen 10 = nativeShiftedFrame 1 (min nativeGap011Old.x nativeGap011Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_010_Gen, nativeHeatStep_hInd_010_Gen]

theorem nativeHeatStepFrameNum_010_Gen : NativeHeatStepFrameNum 10 := by
  have h1 := nativeHeatStep_hOld_010_Gen
  have h2 := nativeHeatStep_hInd_010_Gen
  have h3 := nativeHeatStep_hVar_010_Gen
  have h4 := nativeHeatStep_hQm_010_Gen
  have h5 := nativeHeatStep_hQN_010_Gen
  have h6 := nativeHeatStep_hY0_010_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_010_Gen : NativeHeatStepIndivNum 10 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 10 (by norm_num)) = nativeGap011Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_010_Gen]; exact nativeGap011Old_source
  · rw [hc, nativeHeatStep_hInd_010_Gen]; exact nativeGap011Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_010_Gen : nativeHeatY48Gen 10 = nativeHeat010Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_010_Gen, nativeHeatStep_hFr_010_Gen,
    nativeHeatStep_hCoef_010_Gen, nativeHeatStep_hFixed_010_Gen,
    nativeHeatStep_hBase_010_Gen]
  exact nativeHeat010All48

theorem nativeHeatResultGen_010 : nativeHeatResultGen 10 = nativeHeat010Result := by
  rw [← nativeHeat010Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_010_Gen, nativeHeatStep_hY0_010_Gen, nativeHeatStep_hExp_010_Gen,
    nativeHeatStep_hInit_010_Gen, nativeHeatStep_hFixed_010_Gen]

end ASDExplicitGamma.Native

end
