module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat077Complete
public import ASDExplicitGamma.Numerics.Native.Gap078Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_077_Gen : nativeHeatOldRowGen 77 = nativeGap078Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_077_Gen : nativeHeatIndividualGen 77 = nativeGap078Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_077_Gen : nativeHeatGenVariance 77 = nativeHeat077Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_077_Gen, nativeHeat077Variance_formula]

theorem nativeHeatStep_hSpec_077_Gen : nativeHeatGenSpectral 77 = nativeHeat077Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_077_Gen, nativeHeat077Variance_formula]

theorem nativeHeatStep_hQm_077_Gen : nativeHeatGenQm 77 = nativeHeat077Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_077_Gen, nativeHeatStep_hSpec_077_Gen,
    nativeHeat077Qm_formula]

theorem nativeHeatStep_hQN_077_Gen : nativeHeatQNGen 77 = nativeHeat077QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_077_Gen, nativeHeat077QN_formula]

theorem nativeHeatStep_hFr_077_Gen : nativeHeatFramesGen 77 = nativeHeat077Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_077_Gen, nativeHeatStep_hInd_077_Gen,
    nativeHeatStep_hVar_077_Gen, nativeHeatStep_hQN_077_Gen, nativeHeat077Frames_formula]

theorem nativeHeatStep_hArg_077_Gen : nativeHeatExpArgGen 77 = nativeHeatExpArg nativeGap078Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_077_Gen]

theorem nativeHeatStep_hExp_077_Gen : nativeHeatExpGen 77 = nativeHeat077Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_077_Gen, nativeHeat077Exp_formula]

theorem nativeHeatStep_hCoef_077_Gen : nativeHeatCoefGen 77 = nativeHeat077Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_077_Gen, nativeHeat077Coef_formula]

theorem nativeHeatStep_hInit_077_Gen : nativeHeatInitGen 77 = nativeHeat077Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_077_Gen, nativeHeatStep_hVar_077_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat077Init00_formula
    · exact nativeHeat077Init01_formula
    · exact nativeHeat077Init02_formula
    · exact nativeHeat077Init03_formula
    · exact nativeHeat077Init04_formula
    · exact nativeHeat077Init05_formula
    · exact nativeHeat077Init06_formula
    · exact nativeHeat077Init07_formula
    · exact nativeHeat077Init08_formula
    · exact nativeHeat077Init09_formula
    · exact nativeHeat077Init10_formula
    · exact nativeHeat077Init11_formula
    · exact nativeHeat077Init12_formula
    · exact nativeHeat077Init13_formula
    · exact nativeHeat077Init14_formula
    · exact nativeHeat077Init15_formula
    · exact nativeHeat077Init16_formula
    · exact nativeHeat077Init17_formula
    · exact nativeHeat077Init18_formula
    · exact nativeHeat077Init19_formula
    · exact nativeHeat077Init20_formula
theorem nativeHeatStep_hBase_077_Gen : nativeHeatBaseGen 77 = nativeHeat077Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_077_Gen, nativeHeatStep_hInit_077_Gen, nativeHeat077Base_formula]

theorem nativeHeatStep_hFixed_077_Gen : nativeHeatFixedGen 77 = nativeHeat077Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_077_Gen, nativeHeatStep_hFr_077_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat077Fixed01_formula
    · exact nativeHeat077Fixed02_formula
    · exact nativeHeat077Fixed03_formula
    · exact nativeHeat077Fixed04_formula
    · exact nativeHeat077Fixed05_formula
    · exact nativeHeat077Fixed06_formula
    · exact nativeHeat077Fixed07_formula
    · exact nativeHeat077Fixed08_formula
    · exact nativeHeat077Fixed09_formula
    · exact nativeHeat077Fixed10_formula
    · exact nativeHeat077Fixed11_formula
    · exact nativeHeat077Fixed12_formula
    · exact nativeHeat077Fixed13_formula
    · exact nativeHeat077Fixed14_formula
    · exact nativeHeat077Fixed15_formula
    · exact nativeHeat077Fixed16_formula
    · exact nativeHeat077Fixed17_formula
    · exact nativeHeat077Fixed18_formula
    · exact nativeHeat077Fixed19_formula
    · exact nativeHeat077Fixed20_formula

theorem nativeHeatStep_chk_077_Gen :
    nativeHeatPassRootsOk nativeGap078Old nativeHeat077Frames nativeHeat077Coef nativeHeat077Fixed nativeHeat077Base 48 nativeHeat077Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_077_Gen : NativeHeatStepPassNum 77 := by
  refine nativeHeatStepPassNum_of_literals 77 nativeGap078Old nativeHeat077Frames (nativeHeatExpArg nativeGap078Old)
    nativeHeat077Exp nativeHeat077Coef nativeHeat077Fixed nativeHeat077Init nativeHeat077Base nativeHeatStep_hOld_077_Gen
    nativeHeatStep_hFr_077_Gen nativeHeatStep_hArg_077_Gen nativeHeatStep_hExp_077_Gen
    nativeHeatStep_hCoef_077_Gen nativeHeatStep_hFixed_077_Gen
    nativeHeatStep_hInit_077_Gen nativeHeatStep_hBase_077_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_077_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_077_Gen :
    nativeHeatY0Gen 77 = nativeShiftedFrame 1 (min nativeGap078Old.x nativeGap078Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_077_Gen, nativeHeatStep_hInd_077_Gen]

theorem nativeHeatStepFrameNum_077_Gen : NativeHeatStepFrameNum 77 := by
  have h1 := nativeHeatStep_hOld_077_Gen
  have h2 := nativeHeatStep_hInd_077_Gen
  have h3 := nativeHeatStep_hVar_077_Gen
  have h4 := nativeHeatStep_hQm_077_Gen
  have h5 := nativeHeatStep_hQN_077_Gen
  have h6 := nativeHeatStep_hY0_077_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_077_Gen : NativeHeatStepIndivNum 77 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 77 (by norm_num)) = nativeGap078Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_077_Gen]; exact nativeGap078Old_source
  · rw [hc, nativeHeatStep_hInd_077_Gen]; exact nativeGap078Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_077_Gen : nativeHeatY48Gen 77 = nativeHeat077Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_077_Gen, nativeHeatStep_hFr_077_Gen,
    nativeHeatStep_hCoef_077_Gen, nativeHeatStep_hFixed_077_Gen,
    nativeHeatStep_hBase_077_Gen]
  exact nativeHeat077All48

theorem nativeHeatResultGen_077 : nativeHeatResultGen 77 = nativeHeat077Result := by
  rw [← nativeHeat077Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_077_Gen, nativeHeatStep_hY0_077_Gen, nativeHeatStep_hExp_077_Gen,
    nativeHeatStep_hInit_077_Gen, nativeHeatStep_hFixed_077_Gen]

end ASDExplicitGamma.Native

end
