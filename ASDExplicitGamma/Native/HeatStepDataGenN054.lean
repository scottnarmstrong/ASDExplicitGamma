module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat054Complete
public import ASDExplicitGamma.Numerics.Native.Gap055Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_054_Gen : nativeHeatOldRowGen 54 = nativeGap055Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_054_Gen : nativeHeatIndividualGen 54 = nativeGap055Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_054_Gen : nativeHeatGenVariance 54 = nativeHeat054Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_054_Gen, nativeHeat054Variance_formula]

theorem nativeHeatStep_hSpec_054_Gen : nativeHeatGenSpectral 54 = nativeHeat054Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_054_Gen, nativeHeat054Variance_formula]

theorem nativeHeatStep_hQm_054_Gen : nativeHeatGenQm 54 = nativeHeat054Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_054_Gen, nativeHeatStep_hSpec_054_Gen,
    nativeHeat054Qm_formula]

theorem nativeHeatStep_hQN_054_Gen : nativeHeatQNGen 54 = nativeHeat054QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_054_Gen, nativeHeat054QN_formula]

theorem nativeHeatStep_hFr_054_Gen : nativeHeatFramesGen 54 = nativeHeat054Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_054_Gen, nativeHeatStep_hInd_054_Gen,
    nativeHeatStep_hVar_054_Gen, nativeHeatStep_hQN_054_Gen, nativeHeat054Frames_formula]

theorem nativeHeatStep_hArg_054_Gen : nativeHeatExpArgGen 54 = nativeHeatExpArg nativeGap055Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_054_Gen]

theorem nativeHeatStep_hExp_054_Gen : nativeHeatExpGen 54 = nativeHeat054Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_054_Gen, nativeHeat054Exp_formula]

theorem nativeHeatStep_hCoef_054_Gen : nativeHeatCoefGen 54 = nativeHeat054Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_054_Gen, nativeHeat054Coef_formula]

theorem nativeHeatStep_hInit_054_Gen : nativeHeatInitGen 54 = nativeHeat054Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_054_Gen, nativeHeatStep_hVar_054_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat054Init00_formula
    · exact nativeHeat054Init01_formula
    · exact nativeHeat054Init02_formula
    · exact nativeHeat054Init03_formula
    · exact nativeHeat054Init04_formula
    · exact nativeHeat054Init05_formula
    · exact nativeHeat054Init06_formula
    · exact nativeHeat054Init07_formula
    · exact nativeHeat054Init08_formula
    · exact nativeHeat054Init09_formula
    · exact nativeHeat054Init10_formula
    · exact nativeHeat054Init11_formula
    · exact nativeHeat054Init12_formula
    · exact nativeHeat054Init13_formula
    · exact nativeHeat054Init14_formula
    · exact nativeHeat054Init15_formula
    · exact nativeHeat054Init16_formula
    · exact nativeHeat054Init17_formula
    · exact nativeHeat054Init18_formula
    · exact nativeHeat054Init19_formula
    · exact nativeHeat054Init20_formula
theorem nativeHeatStep_hBase_054_Gen : nativeHeatBaseGen 54 = nativeHeat054Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_054_Gen, nativeHeatStep_hInit_054_Gen, nativeHeat054Base_formula]

theorem nativeHeatStep_hFixed_054_Gen : nativeHeatFixedGen 54 = nativeHeat054Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_054_Gen, nativeHeatStep_hFr_054_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat054Fixed01_formula
    · exact nativeHeat054Fixed02_formula
    · exact nativeHeat054Fixed03_formula
    · exact nativeHeat054Fixed04_formula
    · exact nativeHeat054Fixed05_formula
    · exact nativeHeat054Fixed06_formula
    · exact nativeHeat054Fixed07_formula
    · exact nativeHeat054Fixed08_formula
    · exact nativeHeat054Fixed09_formula
    · exact nativeHeat054Fixed10_formula
    · exact nativeHeat054Fixed11_formula
    · exact nativeHeat054Fixed12_formula
    · exact nativeHeat054Fixed13_formula
    · exact nativeHeat054Fixed14_formula
    · exact nativeHeat054Fixed15_formula
    · exact nativeHeat054Fixed16_formula
    · exact nativeHeat054Fixed17_formula
    · exact nativeHeat054Fixed18_formula
    · exact nativeHeat054Fixed19_formula
    · exact nativeHeat054Fixed20_formula

theorem nativeHeatStep_chk_054_Gen :
    nativeHeatPassRootsOk nativeGap055Old nativeHeat054Frames nativeHeat054Coef nativeHeat054Fixed nativeHeat054Base 48 nativeHeat054Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_054_Gen : NativeHeatStepPassNum 54 := by
  refine nativeHeatStepPassNum_of_literals 54 nativeGap055Old nativeHeat054Frames (nativeHeatExpArg nativeGap055Old)
    nativeHeat054Exp nativeHeat054Coef nativeHeat054Fixed nativeHeat054Init nativeHeat054Base nativeHeatStep_hOld_054_Gen
    nativeHeatStep_hFr_054_Gen nativeHeatStep_hArg_054_Gen nativeHeatStep_hExp_054_Gen
    nativeHeatStep_hCoef_054_Gen nativeHeatStep_hFixed_054_Gen
    nativeHeatStep_hInit_054_Gen nativeHeatStep_hBase_054_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_054_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_054_Gen :
    nativeHeatY0Gen 54 = nativeShiftedFrame 1 (min nativeGap055Old.x nativeGap055Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_054_Gen, nativeHeatStep_hInd_054_Gen]

theorem nativeHeatStepFrameNum_054_Gen : NativeHeatStepFrameNum 54 := by
  have h1 := nativeHeatStep_hOld_054_Gen
  have h2 := nativeHeatStep_hInd_054_Gen
  have h3 := nativeHeatStep_hVar_054_Gen
  have h4 := nativeHeatStep_hQm_054_Gen
  have h5 := nativeHeatStep_hQN_054_Gen
  have h6 := nativeHeatStep_hY0_054_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_054_Gen : NativeHeatStepIndivNum 54 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 54 (by norm_num)) = nativeGap055Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_054_Gen]; exact nativeGap055Old_source
  · rw [hc, nativeHeatStep_hInd_054_Gen]; exact nativeGap055Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_054_Gen : nativeHeatY48Gen 54 = nativeHeat054Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_054_Gen, nativeHeatStep_hFr_054_Gen,
    nativeHeatStep_hCoef_054_Gen, nativeHeatStep_hFixed_054_Gen,
    nativeHeatStep_hBase_054_Gen]
  exact nativeHeat054All48

theorem nativeHeatResultGen_054 : nativeHeatResultGen 54 = nativeHeat054Result := by
  rw [← nativeHeat054Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_054_Gen, nativeHeatStep_hY0_054_Gen, nativeHeatStep_hExp_054_Gen,
    nativeHeatStep_hInit_054_Gen, nativeHeatStep_hFixed_054_Gen]

end ASDExplicitGamma.Native

end
