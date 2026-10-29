module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat065Complete
public import ASDExplicitGamma.Numerics.Native.Gap066Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_065_Gen : nativeHeatOldRowGen 65 = nativeGap066Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_065_Gen : nativeHeatIndividualGen 65 = nativeGap066Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_065_Gen : nativeHeatGenVariance 65 = nativeHeat065Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_065_Gen, nativeHeat065Variance_formula]

theorem nativeHeatStep_hSpec_065_Gen : nativeHeatGenSpectral 65 = nativeHeat065Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_065_Gen, nativeHeat065Variance_formula]

theorem nativeHeatStep_hQm_065_Gen : nativeHeatGenQm 65 = nativeHeat065Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_065_Gen, nativeHeatStep_hSpec_065_Gen,
    nativeHeat065Qm_formula]

theorem nativeHeatStep_hQN_065_Gen : nativeHeatQNGen 65 = nativeHeat065QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_065_Gen, nativeHeat065QN_formula]

theorem nativeHeatStep_hFr_065_Gen : nativeHeatFramesGen 65 = nativeHeat065Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_065_Gen, nativeHeatStep_hInd_065_Gen,
    nativeHeatStep_hVar_065_Gen, nativeHeatStep_hQN_065_Gen, nativeHeat065Frames_formula]

theorem nativeHeatStep_hArg_065_Gen : nativeHeatExpArgGen 65 = nativeHeatExpArg nativeGap066Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_065_Gen]

theorem nativeHeatStep_hExp_065_Gen : nativeHeatExpGen 65 = nativeHeat065Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_065_Gen, nativeHeat065Exp_formula]

theorem nativeHeatStep_hCoef_065_Gen : nativeHeatCoefGen 65 = nativeHeat065Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_065_Gen, nativeHeat065Coef_formula]

theorem nativeHeatStep_hInit_065_Gen : nativeHeatInitGen 65 = nativeHeat065Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_065_Gen, nativeHeatStep_hVar_065_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat065Init00_formula
    · exact nativeHeat065Init01_formula
    · exact nativeHeat065Init02_formula
    · exact nativeHeat065Init03_formula
    · exact nativeHeat065Init04_formula
    · exact nativeHeat065Init05_formula
    · exact nativeHeat065Init06_formula
    · exact nativeHeat065Init07_formula
    · exact nativeHeat065Init08_formula
    · exact nativeHeat065Init09_formula
    · exact nativeHeat065Init10_formula
    · exact nativeHeat065Init11_formula
    · exact nativeHeat065Init12_formula
    · exact nativeHeat065Init13_formula
    · exact nativeHeat065Init14_formula
    · exact nativeHeat065Init15_formula
    · exact nativeHeat065Init16_formula
    · exact nativeHeat065Init17_formula
    · exact nativeHeat065Init18_formula
    · exact nativeHeat065Init19_formula
    · exact nativeHeat065Init20_formula
theorem nativeHeatStep_hBase_065_Gen : nativeHeatBaseGen 65 = nativeHeat065Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_065_Gen, nativeHeatStep_hInit_065_Gen, nativeHeat065Base_formula]

theorem nativeHeatStep_hFixed_065_Gen : nativeHeatFixedGen 65 = nativeHeat065Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_065_Gen, nativeHeatStep_hFr_065_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat065Fixed01_formula
    · exact nativeHeat065Fixed02_formula
    · exact nativeHeat065Fixed03_formula
    · exact nativeHeat065Fixed04_formula
    · exact nativeHeat065Fixed05_formula
    · exact nativeHeat065Fixed06_formula
    · exact nativeHeat065Fixed07_formula
    · exact nativeHeat065Fixed08_formula
    · exact nativeHeat065Fixed09_formula
    · exact nativeHeat065Fixed10_formula
    · exact nativeHeat065Fixed11_formula
    · exact nativeHeat065Fixed12_formula
    · exact nativeHeat065Fixed13_formula
    · exact nativeHeat065Fixed14_formula
    · exact nativeHeat065Fixed15_formula
    · exact nativeHeat065Fixed16_formula
    · exact nativeHeat065Fixed17_formula
    · exact nativeHeat065Fixed18_formula
    · exact nativeHeat065Fixed19_formula
    · exact nativeHeat065Fixed20_formula

theorem nativeHeatStep_chk_065_Gen :
    nativeHeatPassRootsOk nativeGap066Old nativeHeat065Frames nativeHeat065Coef nativeHeat065Fixed nativeHeat065Base 48 nativeHeat065Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_065_Gen : NativeHeatStepPassNum 65 := by
  refine nativeHeatStepPassNum_of_literals 65 nativeGap066Old nativeHeat065Frames (nativeHeatExpArg nativeGap066Old)
    nativeHeat065Exp nativeHeat065Coef nativeHeat065Fixed nativeHeat065Init nativeHeat065Base nativeHeatStep_hOld_065_Gen
    nativeHeatStep_hFr_065_Gen nativeHeatStep_hArg_065_Gen nativeHeatStep_hExp_065_Gen
    nativeHeatStep_hCoef_065_Gen nativeHeatStep_hFixed_065_Gen
    nativeHeatStep_hInit_065_Gen nativeHeatStep_hBase_065_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_065_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_065_Gen :
    nativeHeatY0Gen 65 = nativeShiftedFrame 1 (min nativeGap066Old.x nativeGap066Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_065_Gen, nativeHeatStep_hInd_065_Gen]

theorem nativeHeatStepFrameNum_065_Gen : NativeHeatStepFrameNum 65 := by
  have h1 := nativeHeatStep_hOld_065_Gen
  have h2 := nativeHeatStep_hInd_065_Gen
  have h3 := nativeHeatStep_hVar_065_Gen
  have h4 := nativeHeatStep_hQm_065_Gen
  have h5 := nativeHeatStep_hQN_065_Gen
  have h6 := nativeHeatStep_hY0_065_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_065_Gen : NativeHeatStepIndivNum 65 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 65 (by norm_num)) = nativeGap066Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_065_Gen]; exact nativeGap066Old_source
  · rw [hc, nativeHeatStep_hInd_065_Gen]; exact nativeGap066Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_065_Gen : nativeHeatY48Gen 65 = nativeHeat065Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_065_Gen, nativeHeatStep_hFr_065_Gen,
    nativeHeatStep_hCoef_065_Gen, nativeHeatStep_hFixed_065_Gen,
    nativeHeatStep_hBase_065_Gen]
  exact nativeHeat065All48

theorem nativeHeatResultGen_065 : nativeHeatResultGen 65 = nativeHeat065Result := by
  rw [← nativeHeat065Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_065_Gen, nativeHeatStep_hY0_065_Gen, nativeHeatStep_hExp_065_Gen,
    nativeHeatStep_hInit_065_Gen, nativeHeatStep_hFixed_065_Gen]

end ASDExplicitGamma.Native

end
