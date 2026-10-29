module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat132Complete
public import ASDExplicitGamma.Numerics.Native.Gap133Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_132_Gen : nativeHeatOldRowGen 132 = nativeGap133Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_132_Gen : nativeHeatIndividualGen 132 = nativeGap133Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_132_Gen : nativeHeatGenVariance 132 = nativeHeat132Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_132_Gen, nativeHeat132Variance_formula]

theorem nativeHeatStep_hSpec_132_Gen : nativeHeatGenSpectral 132 = nativeHeat132Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_132_Gen, nativeHeat132Variance_formula]

theorem nativeHeatStep_hQm_132_Gen : nativeHeatGenQm 132 = nativeHeat132Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_132_Gen, nativeHeatStep_hSpec_132_Gen,
    nativeHeat132Qm_formula]

theorem nativeHeatStep_hQN_132_Gen : nativeHeatQNGen 132 = nativeHeat132QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_132_Gen, nativeHeat132QN_formula]

theorem nativeHeatStep_hFr_132_Gen : nativeHeatFramesGen 132 = nativeHeat132Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_132_Gen, nativeHeatStep_hInd_132_Gen,
    nativeHeatStep_hVar_132_Gen, nativeHeatStep_hQN_132_Gen, nativeHeat132Frames_formula]

theorem nativeHeatStep_hArg_132_Gen : nativeHeatExpArgGen 132 = nativeHeatExpArg nativeGap133Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_132_Gen]

theorem nativeHeatStep_hExp_132_Gen : nativeHeatExpGen 132 = nativeHeat132Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_132_Gen, nativeHeat132Exp_formula]

theorem nativeHeatStep_hCoef_132_Gen : nativeHeatCoefGen 132 = nativeHeat132Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_132_Gen, nativeHeat132Coef_formula]

theorem nativeHeatStep_hInit_132_Gen : nativeHeatInitGen 132 = nativeHeat132Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_132_Gen, nativeHeatStep_hVar_132_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat132Init00_formula
    · exact nativeHeat132Init01_formula
    · exact nativeHeat132Init02_formula
    · exact nativeHeat132Init03_formula
    · exact nativeHeat132Init04_formula
    · exact nativeHeat132Init05_formula
    · exact nativeHeat132Init06_formula
    · exact nativeHeat132Init07_formula
    · exact nativeHeat132Init08_formula
    · exact nativeHeat132Init09_formula
    · exact nativeHeat132Init10_formula
    · exact nativeHeat132Init11_formula
    · exact nativeHeat132Init12_formula
    · exact nativeHeat132Init13_formula
    · exact nativeHeat132Init14_formula
    · exact nativeHeat132Init15_formula
    · exact nativeHeat132Init16_formula
    · exact nativeHeat132Init17_formula
    · exact nativeHeat132Init18_formula
    · exact nativeHeat132Init19_formula
    · exact nativeHeat132Init20_formula
theorem nativeHeatStep_hBase_132_Gen : nativeHeatBaseGen 132 = nativeHeat132Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_132_Gen, nativeHeatStep_hInit_132_Gen, nativeHeat132Base_formula]

theorem nativeHeatStep_hFixed_132_Gen : nativeHeatFixedGen 132 = nativeHeat132Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_132_Gen, nativeHeatStep_hFr_132_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat132Fixed01_formula
    · exact nativeHeat132Fixed02_formula
    · exact nativeHeat132Fixed03_formula
    · exact nativeHeat132Fixed04_formula
    · exact nativeHeat132Fixed05_formula
    · exact nativeHeat132Fixed06_formula
    · exact nativeHeat132Fixed07_formula
    · exact nativeHeat132Fixed08_formula
    · exact nativeHeat132Fixed09_formula
    · exact nativeHeat132Fixed10_formula
    · exact nativeHeat132Fixed11_formula
    · exact nativeHeat132Fixed12_formula
    · exact nativeHeat132Fixed13_formula
    · exact nativeHeat132Fixed14_formula
    · exact nativeHeat132Fixed15_formula
    · exact nativeHeat132Fixed16_formula
    · exact nativeHeat132Fixed17_formula
    · exact nativeHeat132Fixed18_formula
    · exact nativeHeat132Fixed19_formula
    · exact nativeHeat132Fixed20_formula

theorem nativeHeatStep_chk_132_Gen :
    nativeHeatPassRootsOk nativeGap133Old nativeHeat132Frames nativeHeat132Coef nativeHeat132Fixed nativeHeat132Base 48 nativeHeat132Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_132_Gen : NativeHeatStepPassNum 132 := by
  refine nativeHeatStepPassNum_of_literals 132 nativeGap133Old nativeHeat132Frames (nativeHeatExpArg nativeGap133Old)
    nativeHeat132Exp nativeHeat132Coef nativeHeat132Fixed nativeHeat132Init nativeHeat132Base nativeHeatStep_hOld_132_Gen
    nativeHeatStep_hFr_132_Gen nativeHeatStep_hArg_132_Gen nativeHeatStep_hExp_132_Gen
    nativeHeatStep_hCoef_132_Gen nativeHeatStep_hFixed_132_Gen
    nativeHeatStep_hInit_132_Gen nativeHeatStep_hBase_132_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_132_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_132_Gen :
    nativeHeatY0Gen 132 = nativeShiftedFrame 1 (min nativeGap133Old.x nativeGap133Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_132_Gen, nativeHeatStep_hInd_132_Gen]

theorem nativeHeatStepFrameNum_132_Gen : NativeHeatStepFrameNum 132 := by
  have h1 := nativeHeatStep_hOld_132_Gen
  have h2 := nativeHeatStep_hInd_132_Gen
  have h3 := nativeHeatStep_hVar_132_Gen
  have h4 := nativeHeatStep_hQm_132_Gen
  have h5 := nativeHeatStep_hQN_132_Gen
  have h6 := nativeHeatStep_hY0_132_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_132_Gen : NativeHeatStepIndivNum 132 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 132 (by norm_num)) = nativeGap133Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_132_Gen]; exact nativeGap133Old_source
  · rw [hc, nativeHeatStep_hInd_132_Gen]; exact nativeGap133Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_132_Gen : nativeHeatY48Gen 132 = nativeHeat132Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_132_Gen, nativeHeatStep_hFr_132_Gen,
    nativeHeatStep_hCoef_132_Gen, nativeHeatStep_hFixed_132_Gen,
    nativeHeatStep_hBase_132_Gen]
  exact nativeHeat132All48

theorem nativeHeatResultGen_132 : nativeHeatResultGen 132 = nativeHeat132Result := by
  rw [← nativeHeat132Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_132_Gen, nativeHeatStep_hY0_132_Gen, nativeHeatStep_hExp_132_Gen,
    nativeHeatStep_hInit_132_Gen, nativeHeatStep_hFixed_132_Gen]

end ASDExplicitGamma.Native

end
