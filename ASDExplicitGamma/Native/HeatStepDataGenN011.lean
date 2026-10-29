module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat011Complete
public import ASDExplicitGamma.Numerics.Native.Gap012Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_011_Gen : nativeHeatOldRowGen 11 = nativeGap012Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_011_Gen : nativeHeatIndividualGen 11 = nativeGap012Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_011_Gen : nativeHeatGenVariance 11 = nativeHeat011Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_011_Gen, nativeHeat011Variance_formula]

theorem nativeHeatStep_hSpec_011_Gen : nativeHeatGenSpectral 11 = nativeHeat011Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_011_Gen, nativeHeat011Variance_formula]

theorem nativeHeatStep_hQm_011_Gen : nativeHeatGenQm 11 = nativeHeat011Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_011_Gen, nativeHeatStep_hSpec_011_Gen,
    nativeHeat011Qm_formula]

theorem nativeHeatStep_hQN_011_Gen : nativeHeatQNGen 11 = nativeHeat011QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_011_Gen, nativeHeat011QN_formula]

theorem nativeHeatStep_hFr_011_Gen : nativeHeatFramesGen 11 = nativeHeat011Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_011_Gen, nativeHeatStep_hInd_011_Gen,
    nativeHeatStep_hVar_011_Gen, nativeHeatStep_hQN_011_Gen, nativeHeat011Frames_formula]

theorem nativeHeatStep_hArg_011_Gen : nativeHeatExpArgGen 11 = nativeHeatExpArg nativeGap012Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_011_Gen]

theorem nativeHeatStep_hExp_011_Gen : nativeHeatExpGen 11 = nativeHeat011Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_011_Gen, nativeHeat011Exp_formula]

theorem nativeHeatStep_hCoef_011_Gen : nativeHeatCoefGen 11 = nativeHeat011Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_011_Gen, nativeHeat011Coef_formula]

theorem nativeHeatStep_hInit_011_Gen : nativeHeatInitGen 11 = nativeHeat011Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_011_Gen, nativeHeatStep_hVar_011_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat011Init00_formula
    · exact nativeHeat011Init01_formula
    · exact nativeHeat011Init02_formula
    · exact nativeHeat011Init03_formula
    · exact nativeHeat011Init04_formula
    · exact nativeHeat011Init05_formula
    · exact nativeHeat011Init06_formula
    · exact nativeHeat011Init07_formula
    · exact nativeHeat011Init08_formula
    · exact nativeHeat011Init09_formula
    · exact nativeHeat011Init10_formula
    · exact nativeHeat011Init11_formula
    · exact nativeHeat011Init12_formula
    · exact nativeHeat011Init13_formula
    · exact nativeHeat011Init14_formula
    · exact nativeHeat011Init15_formula
    · exact nativeHeat011Init16_formula
    · exact nativeHeat011Init17_formula
    · exact nativeHeat011Init18_formula
    · exact nativeHeat011Init19_formula
    · exact nativeHeat011Init20_formula
theorem nativeHeatStep_hBase_011_Gen : nativeHeatBaseGen 11 = nativeHeat011Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_011_Gen, nativeHeatStep_hInit_011_Gen, nativeHeat011Base_formula]

theorem nativeHeatStep_hFixed_011_Gen : nativeHeatFixedGen 11 = nativeHeat011Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_011_Gen, nativeHeatStep_hFr_011_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat011Fixed01_formula
    · exact nativeHeat011Fixed02_formula
    · exact nativeHeat011Fixed03_formula
    · exact nativeHeat011Fixed04_formula
    · exact nativeHeat011Fixed05_formula
    · exact nativeHeat011Fixed06_formula
    · exact nativeHeat011Fixed07_formula
    · exact nativeHeat011Fixed08_formula
    · exact nativeHeat011Fixed09_formula
    · exact nativeHeat011Fixed10_formula
    · exact nativeHeat011Fixed11_formula
    · exact nativeHeat011Fixed12_formula
    · exact nativeHeat011Fixed13_formula
    · exact nativeHeat011Fixed14_formula
    · exact nativeHeat011Fixed15_formula
    · exact nativeHeat011Fixed16_formula
    · exact nativeHeat011Fixed17_formula
    · exact nativeHeat011Fixed18_formula
    · exact nativeHeat011Fixed19_formula
    · exact nativeHeat011Fixed20_formula

theorem nativeHeatStep_chk_011_Gen :
    nativeHeatPassRootsOk nativeGap012Old nativeHeat011Frames nativeHeat011Coef nativeHeat011Fixed nativeHeat011Base 48 nativeHeat011Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_011_Gen : NativeHeatStepPassNum 11 := by
  refine nativeHeatStepPassNum_of_literals 11 nativeGap012Old nativeHeat011Frames (nativeHeatExpArg nativeGap012Old)
    nativeHeat011Exp nativeHeat011Coef nativeHeat011Fixed nativeHeat011Init nativeHeat011Base nativeHeatStep_hOld_011_Gen
    nativeHeatStep_hFr_011_Gen nativeHeatStep_hArg_011_Gen nativeHeatStep_hExp_011_Gen
    nativeHeatStep_hCoef_011_Gen nativeHeatStep_hFixed_011_Gen
    nativeHeatStep_hInit_011_Gen nativeHeatStep_hBase_011_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_011_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_011_Gen :
    nativeHeatY0Gen 11 = nativeShiftedFrame 1 (min nativeGap012Old.x nativeGap012Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_011_Gen, nativeHeatStep_hInd_011_Gen]

theorem nativeHeatStepFrameNum_011_Gen : NativeHeatStepFrameNum 11 := by
  have h1 := nativeHeatStep_hOld_011_Gen
  have h2 := nativeHeatStep_hInd_011_Gen
  have h3 := nativeHeatStep_hVar_011_Gen
  have h4 := nativeHeatStep_hQm_011_Gen
  have h5 := nativeHeatStep_hQN_011_Gen
  have h6 := nativeHeatStep_hY0_011_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_011_Gen : NativeHeatStepIndivNum 11 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 11 (by norm_num)) = nativeGap012Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_011_Gen]; exact nativeGap012Old_source
  · rw [hc, nativeHeatStep_hInd_011_Gen]; exact nativeGap012Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_011_Gen : nativeHeatY48Gen 11 = nativeHeat011Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_011_Gen, nativeHeatStep_hFr_011_Gen,
    nativeHeatStep_hCoef_011_Gen, nativeHeatStep_hFixed_011_Gen,
    nativeHeatStep_hBase_011_Gen]
  exact nativeHeat011All48

theorem nativeHeatResultGen_011 : nativeHeatResultGen 11 = nativeHeat011Result := by
  rw [← nativeHeat011Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_011_Gen, nativeHeatStep_hY0_011_Gen, nativeHeatStep_hExp_011_Gen,
    nativeHeatStep_hInit_011_Gen, nativeHeatStep_hFixed_011_Gen]

end ASDExplicitGamma.Native

end
