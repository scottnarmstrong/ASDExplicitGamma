module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat097Complete
public import ASDExplicitGamma.Numerics.Native.Gap098Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_097_Gen : nativeHeatOldRowGen 97 = nativeGap098Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_097_Gen : nativeHeatIndividualGen 97 = nativeGap098Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_097_Gen : nativeHeatGenVariance 97 = nativeHeat097Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_097_Gen, nativeHeat097Variance_formula]

theorem nativeHeatStep_hSpec_097_Gen : nativeHeatGenSpectral 97 = nativeHeat097Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_097_Gen, nativeHeat097Variance_formula]

theorem nativeHeatStep_hQm_097_Gen : nativeHeatGenQm 97 = nativeHeat097Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_097_Gen, nativeHeatStep_hSpec_097_Gen,
    nativeHeat097Qm_formula]

theorem nativeHeatStep_hQN_097_Gen : nativeHeatQNGen 97 = nativeHeat097QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_097_Gen, nativeHeat097QN_formula]

theorem nativeHeatStep_hFr_097_Gen : nativeHeatFramesGen 97 = nativeHeat097Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_097_Gen, nativeHeatStep_hInd_097_Gen,
    nativeHeatStep_hVar_097_Gen, nativeHeatStep_hQN_097_Gen, nativeHeat097Frames_formula]

theorem nativeHeatStep_hArg_097_Gen : nativeHeatExpArgGen 97 = nativeHeatExpArg nativeGap098Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_097_Gen]

theorem nativeHeatStep_hExp_097_Gen : nativeHeatExpGen 97 = nativeHeat097Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_097_Gen, nativeHeat097Exp_formula]

theorem nativeHeatStep_hCoef_097_Gen : nativeHeatCoefGen 97 = nativeHeat097Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_097_Gen, nativeHeat097Coef_formula]

theorem nativeHeatStep_hInit_097_Gen : nativeHeatInitGen 97 = nativeHeat097Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_097_Gen, nativeHeatStep_hVar_097_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat097Init00_formula
    · exact nativeHeat097Init01_formula
    · exact nativeHeat097Init02_formula
    · exact nativeHeat097Init03_formula
    · exact nativeHeat097Init04_formula
    · exact nativeHeat097Init05_formula
    · exact nativeHeat097Init06_formula
    · exact nativeHeat097Init07_formula
    · exact nativeHeat097Init08_formula
    · exact nativeHeat097Init09_formula
    · exact nativeHeat097Init10_formula
    · exact nativeHeat097Init11_formula
    · exact nativeHeat097Init12_formula
    · exact nativeHeat097Init13_formula
    · exact nativeHeat097Init14_formula
    · exact nativeHeat097Init15_formula
    · exact nativeHeat097Init16_formula
    · exact nativeHeat097Init17_formula
    · exact nativeHeat097Init18_formula
    · exact nativeHeat097Init19_formula
    · exact nativeHeat097Init20_formula
theorem nativeHeatStep_hBase_097_Gen : nativeHeatBaseGen 97 = nativeHeat097Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_097_Gen, nativeHeatStep_hInit_097_Gen, nativeHeat097Base_formula]

theorem nativeHeatStep_hFixed_097_Gen : nativeHeatFixedGen 97 = nativeHeat097Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_097_Gen, nativeHeatStep_hFr_097_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat097Fixed01_formula
    · exact nativeHeat097Fixed02_formula
    · exact nativeHeat097Fixed03_formula
    · exact nativeHeat097Fixed04_formula
    · exact nativeHeat097Fixed05_formula
    · exact nativeHeat097Fixed06_formula
    · exact nativeHeat097Fixed07_formula
    · exact nativeHeat097Fixed08_formula
    · exact nativeHeat097Fixed09_formula
    · exact nativeHeat097Fixed10_formula
    · exact nativeHeat097Fixed11_formula
    · exact nativeHeat097Fixed12_formula
    · exact nativeHeat097Fixed13_formula
    · exact nativeHeat097Fixed14_formula
    · exact nativeHeat097Fixed15_formula
    · exact nativeHeat097Fixed16_formula
    · exact nativeHeat097Fixed17_formula
    · exact nativeHeat097Fixed18_formula
    · exact nativeHeat097Fixed19_formula
    · exact nativeHeat097Fixed20_formula

theorem nativeHeatStep_chk_097_Gen :
    nativeHeatPassRootsOk nativeGap098Old nativeHeat097Frames nativeHeat097Coef nativeHeat097Fixed nativeHeat097Base 48 nativeHeat097Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_097_Gen : NativeHeatStepPassNum 97 := by
  refine nativeHeatStepPassNum_of_literals 97 nativeGap098Old nativeHeat097Frames (nativeHeatExpArg nativeGap098Old)
    nativeHeat097Exp nativeHeat097Coef nativeHeat097Fixed nativeHeat097Init nativeHeat097Base nativeHeatStep_hOld_097_Gen
    nativeHeatStep_hFr_097_Gen nativeHeatStep_hArg_097_Gen nativeHeatStep_hExp_097_Gen
    nativeHeatStep_hCoef_097_Gen nativeHeatStep_hFixed_097_Gen
    nativeHeatStep_hInit_097_Gen nativeHeatStep_hBase_097_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_097_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_097_Gen :
    nativeHeatY0Gen 97 = nativeShiftedFrame 1 (min nativeGap098Old.x nativeGap098Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_097_Gen, nativeHeatStep_hInd_097_Gen]

theorem nativeHeatStepFrameNum_097_Gen : NativeHeatStepFrameNum 97 := by
  have h1 := nativeHeatStep_hOld_097_Gen
  have h2 := nativeHeatStep_hInd_097_Gen
  have h3 := nativeHeatStep_hVar_097_Gen
  have h4 := nativeHeatStep_hQm_097_Gen
  have h5 := nativeHeatStep_hQN_097_Gen
  have h6 := nativeHeatStep_hY0_097_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_097_Gen : NativeHeatStepIndivNum 97 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 97 (by norm_num)) = nativeGap098Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_097_Gen]; exact nativeGap098Old_source
  · rw [hc, nativeHeatStep_hInd_097_Gen]; exact nativeGap098Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_097_Gen : nativeHeatY48Gen 97 = nativeHeat097Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_097_Gen, nativeHeatStep_hFr_097_Gen,
    nativeHeatStep_hCoef_097_Gen, nativeHeatStep_hFixed_097_Gen,
    nativeHeatStep_hBase_097_Gen]
  exact nativeHeat097All48

theorem nativeHeatResultGen_097 : nativeHeatResultGen 97 = nativeHeat097Result := by
  rw [← nativeHeat097Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_097_Gen, nativeHeatStep_hY0_097_Gen, nativeHeatStep_hExp_097_Gen,
    nativeHeatStep_hInit_097_Gen, nativeHeatStep_hFixed_097_Gen]

end ASDExplicitGamma.Native

end
