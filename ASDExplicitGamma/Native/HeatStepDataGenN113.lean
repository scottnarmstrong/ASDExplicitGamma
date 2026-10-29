module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat113Complete
public import ASDExplicitGamma.Numerics.Native.Gap114Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_113_Gen : nativeHeatOldRowGen 113 = nativeGap114Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_113_Gen : nativeHeatIndividualGen 113 = nativeGap114Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_113_Gen : nativeHeatGenVariance 113 = nativeHeat113Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_113_Gen, nativeHeat113Variance_formula]

theorem nativeHeatStep_hSpec_113_Gen : nativeHeatGenSpectral 113 = nativeHeat113Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_113_Gen, nativeHeat113Variance_formula]

theorem nativeHeatStep_hQm_113_Gen : nativeHeatGenQm 113 = nativeHeat113Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_113_Gen, nativeHeatStep_hSpec_113_Gen,
    nativeHeat113Qm_formula]

theorem nativeHeatStep_hQN_113_Gen : nativeHeatQNGen 113 = nativeHeat113QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_113_Gen, nativeHeat113QN_formula]

theorem nativeHeatStep_hFr_113_Gen : nativeHeatFramesGen 113 = nativeHeat113Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_113_Gen, nativeHeatStep_hInd_113_Gen,
    nativeHeatStep_hVar_113_Gen, nativeHeatStep_hQN_113_Gen, nativeHeat113Frames_formula]

theorem nativeHeatStep_hArg_113_Gen : nativeHeatExpArgGen 113 = nativeHeatExpArg nativeGap114Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_113_Gen]

theorem nativeHeatStep_hExp_113_Gen : nativeHeatExpGen 113 = nativeHeat113Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_113_Gen, nativeHeat113Exp_formula]

theorem nativeHeatStep_hCoef_113_Gen : nativeHeatCoefGen 113 = nativeHeat113Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_113_Gen, nativeHeat113Coef_formula]

theorem nativeHeatStep_hInit_113_Gen : nativeHeatInitGen 113 = nativeHeat113Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_113_Gen, nativeHeatStep_hVar_113_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat113Init00_formula
    · exact nativeHeat113Init01_formula
    · exact nativeHeat113Init02_formula
    · exact nativeHeat113Init03_formula
    · exact nativeHeat113Init04_formula
    · exact nativeHeat113Init05_formula
    · exact nativeHeat113Init06_formula
    · exact nativeHeat113Init07_formula
    · exact nativeHeat113Init08_formula
    · exact nativeHeat113Init09_formula
    · exact nativeHeat113Init10_formula
    · exact nativeHeat113Init11_formula
    · exact nativeHeat113Init12_formula
    · exact nativeHeat113Init13_formula
    · exact nativeHeat113Init14_formula
    · exact nativeHeat113Init15_formula
    · exact nativeHeat113Init16_formula
    · exact nativeHeat113Init17_formula
    · exact nativeHeat113Init18_formula
    · exact nativeHeat113Init19_formula
    · exact nativeHeat113Init20_formula
theorem nativeHeatStep_hBase_113_Gen : nativeHeatBaseGen 113 = nativeHeat113Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_113_Gen, nativeHeatStep_hInit_113_Gen, nativeHeat113Base_formula]

theorem nativeHeatStep_hFixed_113_Gen : nativeHeatFixedGen 113 = nativeHeat113Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_113_Gen, nativeHeatStep_hFr_113_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat113Fixed01_formula
    · exact nativeHeat113Fixed02_formula
    · exact nativeHeat113Fixed03_formula
    · exact nativeHeat113Fixed04_formula
    · exact nativeHeat113Fixed05_formula
    · exact nativeHeat113Fixed06_formula
    · exact nativeHeat113Fixed07_formula
    · exact nativeHeat113Fixed08_formula
    · exact nativeHeat113Fixed09_formula
    · exact nativeHeat113Fixed10_formula
    · exact nativeHeat113Fixed11_formula
    · exact nativeHeat113Fixed12_formula
    · exact nativeHeat113Fixed13_formula
    · exact nativeHeat113Fixed14_formula
    · exact nativeHeat113Fixed15_formula
    · exact nativeHeat113Fixed16_formula
    · exact nativeHeat113Fixed17_formula
    · exact nativeHeat113Fixed18_formula
    · exact nativeHeat113Fixed19_formula
    · exact nativeHeat113Fixed20_formula

theorem nativeHeatStep_chk_113_Gen :
    nativeHeatPassRootsOk nativeGap114Old nativeHeat113Frames nativeHeat113Coef nativeHeat113Fixed nativeHeat113Base 48 nativeHeat113Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_113_Gen : NativeHeatStepPassNum 113 := by
  refine nativeHeatStepPassNum_of_literals 113 nativeGap114Old nativeHeat113Frames (nativeHeatExpArg nativeGap114Old)
    nativeHeat113Exp nativeHeat113Coef nativeHeat113Fixed nativeHeat113Init nativeHeat113Base nativeHeatStep_hOld_113_Gen
    nativeHeatStep_hFr_113_Gen nativeHeatStep_hArg_113_Gen nativeHeatStep_hExp_113_Gen
    nativeHeatStep_hCoef_113_Gen nativeHeatStep_hFixed_113_Gen
    nativeHeatStep_hInit_113_Gen nativeHeatStep_hBase_113_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_113_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_113_Gen :
    nativeHeatY0Gen 113 = nativeShiftedFrame 1 (min nativeGap114Old.x nativeGap114Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_113_Gen, nativeHeatStep_hInd_113_Gen]

theorem nativeHeatStepFrameNum_113_Gen : NativeHeatStepFrameNum 113 := by
  have h1 := nativeHeatStep_hOld_113_Gen
  have h2 := nativeHeatStep_hInd_113_Gen
  have h3 := nativeHeatStep_hVar_113_Gen
  have h4 := nativeHeatStep_hQm_113_Gen
  have h5 := nativeHeatStep_hQN_113_Gen
  have h6 := nativeHeatStep_hY0_113_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_113_Gen : NativeHeatStepIndivNum 113 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 113 (by norm_num)) = nativeGap114Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_113_Gen]; exact nativeGap114Old_source
  · rw [hc, nativeHeatStep_hInd_113_Gen]; exact nativeGap114Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_113_Gen : nativeHeatY48Gen 113 = nativeHeat113Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_113_Gen, nativeHeatStep_hFr_113_Gen,
    nativeHeatStep_hCoef_113_Gen, nativeHeatStep_hFixed_113_Gen,
    nativeHeatStep_hBase_113_Gen]
  exact nativeHeat113All48

theorem nativeHeatResultGen_113 : nativeHeatResultGen 113 = nativeHeat113Result := by
  rw [← nativeHeat113Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_113_Gen, nativeHeatStep_hY0_113_Gen, nativeHeatStep_hExp_113_Gen,
    nativeHeatStep_hInit_113_Gen, nativeHeatStep_hFixed_113_Gen]

end ASDExplicitGamma.Native

end
