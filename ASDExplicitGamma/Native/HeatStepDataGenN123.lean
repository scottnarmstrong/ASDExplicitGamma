module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat123Complete
public import ASDExplicitGamma.Numerics.Native.Gap124Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_123_Gen : nativeHeatOldRowGen 123 = nativeGap124Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_123_Gen : nativeHeatIndividualGen 123 = nativeGap124Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_123_Gen : nativeHeatGenVariance 123 = nativeHeat123Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_123_Gen, nativeHeat123Variance_formula]

theorem nativeHeatStep_hSpec_123_Gen : nativeHeatGenSpectral 123 = nativeHeat123Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_123_Gen, nativeHeat123Variance_formula]

theorem nativeHeatStep_hQm_123_Gen : nativeHeatGenQm 123 = nativeHeat123Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_123_Gen, nativeHeatStep_hSpec_123_Gen,
    nativeHeat123Qm_formula]

theorem nativeHeatStep_hQN_123_Gen : nativeHeatQNGen 123 = nativeHeat123QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_123_Gen, nativeHeat123QN_formula]

theorem nativeHeatStep_hFr_123_Gen : nativeHeatFramesGen 123 = nativeHeat123Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_123_Gen, nativeHeatStep_hInd_123_Gen,
    nativeHeatStep_hVar_123_Gen, nativeHeatStep_hQN_123_Gen, nativeHeat123Frames_formula]

theorem nativeHeatStep_hArg_123_Gen : nativeHeatExpArgGen 123 = nativeHeatExpArg nativeGap124Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_123_Gen]

theorem nativeHeatStep_hExp_123_Gen : nativeHeatExpGen 123 = nativeHeat123Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_123_Gen, nativeHeat123Exp_formula]

theorem nativeHeatStep_hCoef_123_Gen : nativeHeatCoefGen 123 = nativeHeat123Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_123_Gen, nativeHeat123Coef_formula]

theorem nativeHeatStep_hInit_123_Gen : nativeHeatInitGen 123 = nativeHeat123Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_123_Gen, nativeHeatStep_hVar_123_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat123Init00_formula
    · exact nativeHeat123Init01_formula
    · exact nativeHeat123Init02_formula
    · exact nativeHeat123Init03_formula
    · exact nativeHeat123Init04_formula
    · exact nativeHeat123Init05_formula
    · exact nativeHeat123Init06_formula
    · exact nativeHeat123Init07_formula
    · exact nativeHeat123Init08_formula
    · exact nativeHeat123Init09_formula
    · exact nativeHeat123Init10_formula
    · exact nativeHeat123Init11_formula
    · exact nativeHeat123Init12_formula
    · exact nativeHeat123Init13_formula
    · exact nativeHeat123Init14_formula
    · exact nativeHeat123Init15_formula
    · exact nativeHeat123Init16_formula
    · exact nativeHeat123Init17_formula
    · exact nativeHeat123Init18_formula
    · exact nativeHeat123Init19_formula
    · exact nativeHeat123Init20_formula
theorem nativeHeatStep_hBase_123_Gen : nativeHeatBaseGen 123 = nativeHeat123Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_123_Gen, nativeHeatStep_hInit_123_Gen, nativeHeat123Base_formula]

theorem nativeHeatStep_hFixed_123_Gen : nativeHeatFixedGen 123 = nativeHeat123Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_123_Gen, nativeHeatStep_hFr_123_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat123Fixed01_formula
    · exact nativeHeat123Fixed02_formula
    · exact nativeHeat123Fixed03_formula
    · exact nativeHeat123Fixed04_formula
    · exact nativeHeat123Fixed05_formula
    · exact nativeHeat123Fixed06_formula
    · exact nativeHeat123Fixed07_formula
    · exact nativeHeat123Fixed08_formula
    · exact nativeHeat123Fixed09_formula
    · exact nativeHeat123Fixed10_formula
    · exact nativeHeat123Fixed11_formula
    · exact nativeHeat123Fixed12_formula
    · exact nativeHeat123Fixed13_formula
    · exact nativeHeat123Fixed14_formula
    · exact nativeHeat123Fixed15_formula
    · exact nativeHeat123Fixed16_formula
    · exact nativeHeat123Fixed17_formula
    · exact nativeHeat123Fixed18_formula
    · exact nativeHeat123Fixed19_formula
    · exact nativeHeat123Fixed20_formula

theorem nativeHeatStep_chk_123_Gen :
    nativeHeatPassRootsOk nativeGap124Old nativeHeat123Frames nativeHeat123Coef nativeHeat123Fixed nativeHeat123Base 48 nativeHeat123Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_123_Gen : NativeHeatStepPassNum 123 := by
  refine nativeHeatStepPassNum_of_literals 123 nativeGap124Old nativeHeat123Frames (nativeHeatExpArg nativeGap124Old)
    nativeHeat123Exp nativeHeat123Coef nativeHeat123Fixed nativeHeat123Init nativeHeat123Base nativeHeatStep_hOld_123_Gen
    nativeHeatStep_hFr_123_Gen nativeHeatStep_hArg_123_Gen nativeHeatStep_hExp_123_Gen
    nativeHeatStep_hCoef_123_Gen nativeHeatStep_hFixed_123_Gen
    nativeHeatStep_hInit_123_Gen nativeHeatStep_hBase_123_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_123_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_123_Gen :
    nativeHeatY0Gen 123 = nativeShiftedFrame 1 (min nativeGap124Old.x nativeGap124Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_123_Gen, nativeHeatStep_hInd_123_Gen]

theorem nativeHeatStepFrameNum_123_Gen : NativeHeatStepFrameNum 123 := by
  have h1 := nativeHeatStep_hOld_123_Gen
  have h2 := nativeHeatStep_hInd_123_Gen
  have h3 := nativeHeatStep_hVar_123_Gen
  have h4 := nativeHeatStep_hQm_123_Gen
  have h5 := nativeHeatStep_hQN_123_Gen
  have h6 := nativeHeatStep_hY0_123_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_123_Gen : NativeHeatStepIndivNum 123 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 123 (by norm_num)) = nativeGap124Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_123_Gen]; exact nativeGap124Old_source
  · rw [hc, nativeHeatStep_hInd_123_Gen]; exact nativeGap124Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_123_Gen : nativeHeatY48Gen 123 = nativeHeat123Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_123_Gen, nativeHeatStep_hFr_123_Gen,
    nativeHeatStep_hCoef_123_Gen, nativeHeatStep_hFixed_123_Gen,
    nativeHeatStep_hBase_123_Gen]
  exact nativeHeat123All48

theorem nativeHeatResultGen_123 : nativeHeatResultGen 123 = nativeHeat123Result := by
  rw [← nativeHeat123Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_123_Gen, nativeHeatStep_hY0_123_Gen, nativeHeatStep_hExp_123_Gen,
    nativeHeatStep_hInit_123_Gen, nativeHeatStep_hFixed_123_Gen]

end ASDExplicitGamma.Native

end
