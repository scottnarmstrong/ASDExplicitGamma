module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat033Complete
public import ASDExplicitGamma.Numerics.Native.Gap034Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_033_Gen : nativeHeatOldRowGen 33 = nativeGap034Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_033_Gen : nativeHeatIndividualGen 33 = nativeGap034Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_033_Gen : nativeHeatGenVariance 33 = nativeHeat033Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_033_Gen, nativeHeat033Variance_formula]

theorem nativeHeatStep_hSpec_033_Gen : nativeHeatGenSpectral 33 = nativeHeat033Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_033_Gen, nativeHeat033Variance_formula]

theorem nativeHeatStep_hQm_033_Gen : nativeHeatGenQm 33 = nativeHeat033Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_033_Gen, nativeHeatStep_hSpec_033_Gen,
    nativeHeat033Qm_formula]

theorem nativeHeatStep_hQN_033_Gen : nativeHeatQNGen 33 = nativeHeat033QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_033_Gen, nativeHeat033QN_formula]

theorem nativeHeatStep_hFr_033_Gen : nativeHeatFramesGen 33 = nativeHeat033Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_033_Gen, nativeHeatStep_hInd_033_Gen,
    nativeHeatStep_hVar_033_Gen, nativeHeatStep_hQN_033_Gen, nativeHeat033Frames_formula]

theorem nativeHeatStep_hArg_033_Gen : nativeHeatExpArgGen 33 = nativeHeatExpArg nativeGap034Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_033_Gen]

theorem nativeHeatStep_hExp_033_Gen : nativeHeatExpGen 33 = nativeHeat033Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_033_Gen, nativeHeat033Exp_formula]

theorem nativeHeatStep_hCoef_033_Gen : nativeHeatCoefGen 33 = nativeHeat033Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_033_Gen, nativeHeat033Coef_formula]

theorem nativeHeatStep_hInit_033_Gen : nativeHeatInitGen 33 = nativeHeat033Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_033_Gen, nativeHeatStep_hVar_033_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat033Init00_formula
    · exact nativeHeat033Init01_formula
    · exact nativeHeat033Init02_formula
    · exact nativeHeat033Init03_formula
    · exact nativeHeat033Init04_formula
    · exact nativeHeat033Init05_formula
    · exact nativeHeat033Init06_formula
    · exact nativeHeat033Init07_formula
    · exact nativeHeat033Init08_formula
    · exact nativeHeat033Init09_formula
    · exact nativeHeat033Init10_formula
    · exact nativeHeat033Init11_formula
    · exact nativeHeat033Init12_formula
    · exact nativeHeat033Init13_formula
    · exact nativeHeat033Init14_formula
    · exact nativeHeat033Init15_formula
    · exact nativeHeat033Init16_formula
    · exact nativeHeat033Init17_formula
    · exact nativeHeat033Init18_formula
    · exact nativeHeat033Init19_formula
    · exact nativeHeat033Init20_formula
theorem nativeHeatStep_hBase_033_Gen : nativeHeatBaseGen 33 = nativeHeat033Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_033_Gen, nativeHeatStep_hInit_033_Gen, nativeHeat033Base_formula]

theorem nativeHeatStep_hFixed_033_Gen : nativeHeatFixedGen 33 = nativeHeat033Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_033_Gen, nativeHeatStep_hFr_033_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat033Fixed01_formula
    · exact nativeHeat033Fixed02_formula
    · exact nativeHeat033Fixed03_formula
    · exact nativeHeat033Fixed04_formula
    · exact nativeHeat033Fixed05_formula
    · exact nativeHeat033Fixed06_formula
    · exact nativeHeat033Fixed07_formula
    · exact nativeHeat033Fixed08_formula
    · exact nativeHeat033Fixed09_formula
    · exact nativeHeat033Fixed10_formula
    · exact nativeHeat033Fixed11_formula
    · exact nativeHeat033Fixed12_formula
    · exact nativeHeat033Fixed13_formula
    · exact nativeHeat033Fixed14_formula
    · exact nativeHeat033Fixed15_formula
    · exact nativeHeat033Fixed16_formula
    · exact nativeHeat033Fixed17_formula
    · exact nativeHeat033Fixed18_formula
    · exact nativeHeat033Fixed19_formula
    · exact nativeHeat033Fixed20_formula

theorem nativeHeatStep_chk_033_Gen :
    nativeHeatPassRootsOk nativeGap034Old nativeHeat033Frames nativeHeat033Coef nativeHeat033Fixed nativeHeat033Base 48 nativeHeat033Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_033_Gen : NativeHeatStepPassNum 33 := by
  refine nativeHeatStepPassNum_of_literals 33 nativeGap034Old nativeHeat033Frames (nativeHeatExpArg nativeGap034Old)
    nativeHeat033Exp nativeHeat033Coef nativeHeat033Fixed nativeHeat033Init nativeHeat033Base nativeHeatStep_hOld_033_Gen
    nativeHeatStep_hFr_033_Gen nativeHeatStep_hArg_033_Gen nativeHeatStep_hExp_033_Gen
    nativeHeatStep_hCoef_033_Gen nativeHeatStep_hFixed_033_Gen
    nativeHeatStep_hInit_033_Gen nativeHeatStep_hBase_033_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_033_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_033_Gen :
    nativeHeatY0Gen 33 = nativeShiftedFrame 1 (min nativeGap034Old.x nativeGap034Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_033_Gen, nativeHeatStep_hInd_033_Gen]

theorem nativeHeatStepFrameNum_033_Gen : NativeHeatStepFrameNum 33 := by
  have h1 := nativeHeatStep_hOld_033_Gen
  have h2 := nativeHeatStep_hInd_033_Gen
  have h3 := nativeHeatStep_hVar_033_Gen
  have h4 := nativeHeatStep_hQm_033_Gen
  have h5 := nativeHeatStep_hQN_033_Gen
  have h6 := nativeHeatStep_hY0_033_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_033_Gen : NativeHeatStepIndivNum 33 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 33 (by norm_num)) = nativeGap034Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_033_Gen]; exact nativeGap034Old_source
  · rw [hc, nativeHeatStep_hInd_033_Gen]; exact nativeGap034Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_033_Gen : nativeHeatY48Gen 33 = nativeHeat033Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_033_Gen, nativeHeatStep_hFr_033_Gen,
    nativeHeatStep_hCoef_033_Gen, nativeHeatStep_hFixed_033_Gen,
    nativeHeatStep_hBase_033_Gen]
  exact nativeHeat033All48

theorem nativeHeatResultGen_033 : nativeHeatResultGen 33 = nativeHeat033Result := by
  rw [← nativeHeat033Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_033_Gen, nativeHeatStep_hY0_033_Gen, nativeHeatStep_hExp_033_Gen,
    nativeHeatStep_hInit_033_Gen, nativeHeatStep_hFixed_033_Gen]

end ASDExplicitGamma.Native

end
