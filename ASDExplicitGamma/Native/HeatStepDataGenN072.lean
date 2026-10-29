module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat072Complete
public import ASDExplicitGamma.Numerics.Native.Gap073Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_072_Gen : nativeHeatOldRowGen 72 = nativeGap073Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_072_Gen : nativeHeatIndividualGen 72 = nativeGap073Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_072_Gen : nativeHeatGenVariance 72 = nativeHeat072Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_072_Gen, nativeHeat072Variance_formula]

theorem nativeHeatStep_hSpec_072_Gen : nativeHeatGenSpectral 72 = nativeHeat072Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_072_Gen, nativeHeat072Variance_formula]

theorem nativeHeatStep_hQm_072_Gen : nativeHeatGenQm 72 = nativeHeat072Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_072_Gen, nativeHeatStep_hSpec_072_Gen,
    nativeHeat072Qm_formula]

theorem nativeHeatStep_hQN_072_Gen : nativeHeatQNGen 72 = nativeHeat072QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_072_Gen, nativeHeat072QN_formula]

theorem nativeHeatStep_hFr_072_Gen : nativeHeatFramesGen 72 = nativeHeat072Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_072_Gen, nativeHeatStep_hInd_072_Gen,
    nativeHeatStep_hVar_072_Gen, nativeHeatStep_hQN_072_Gen, nativeHeat072Frames_formula]

theorem nativeHeatStep_hArg_072_Gen : nativeHeatExpArgGen 72 = nativeHeatExpArg nativeGap073Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_072_Gen]

theorem nativeHeatStep_hExp_072_Gen : nativeHeatExpGen 72 = nativeHeat072Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_072_Gen, nativeHeat072Exp_formula]

theorem nativeHeatStep_hCoef_072_Gen : nativeHeatCoefGen 72 = nativeHeat072Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_072_Gen, nativeHeat072Coef_formula]

theorem nativeHeatStep_hInit_072_Gen : nativeHeatInitGen 72 = nativeHeat072Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_072_Gen, nativeHeatStep_hVar_072_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat072Init00_formula
    · exact nativeHeat072Init01_formula
    · exact nativeHeat072Init02_formula
    · exact nativeHeat072Init03_formula
    · exact nativeHeat072Init04_formula
    · exact nativeHeat072Init05_formula
    · exact nativeHeat072Init06_formula
    · exact nativeHeat072Init07_formula
    · exact nativeHeat072Init08_formula
    · exact nativeHeat072Init09_formula
    · exact nativeHeat072Init10_formula
    · exact nativeHeat072Init11_formula
    · exact nativeHeat072Init12_formula
    · exact nativeHeat072Init13_formula
    · exact nativeHeat072Init14_formula
    · exact nativeHeat072Init15_formula
    · exact nativeHeat072Init16_formula
    · exact nativeHeat072Init17_formula
    · exact nativeHeat072Init18_formula
    · exact nativeHeat072Init19_formula
    · exact nativeHeat072Init20_formula
theorem nativeHeatStep_hBase_072_Gen : nativeHeatBaseGen 72 = nativeHeat072Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_072_Gen, nativeHeatStep_hInit_072_Gen, nativeHeat072Base_formula]

theorem nativeHeatStep_hFixed_072_Gen : nativeHeatFixedGen 72 = nativeHeat072Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_072_Gen, nativeHeatStep_hFr_072_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat072Fixed01_formula
    · exact nativeHeat072Fixed02_formula
    · exact nativeHeat072Fixed03_formula
    · exact nativeHeat072Fixed04_formula
    · exact nativeHeat072Fixed05_formula
    · exact nativeHeat072Fixed06_formula
    · exact nativeHeat072Fixed07_formula
    · exact nativeHeat072Fixed08_formula
    · exact nativeHeat072Fixed09_formula
    · exact nativeHeat072Fixed10_formula
    · exact nativeHeat072Fixed11_formula
    · exact nativeHeat072Fixed12_formula
    · exact nativeHeat072Fixed13_formula
    · exact nativeHeat072Fixed14_formula
    · exact nativeHeat072Fixed15_formula
    · exact nativeHeat072Fixed16_formula
    · exact nativeHeat072Fixed17_formula
    · exact nativeHeat072Fixed18_formula
    · exact nativeHeat072Fixed19_formula
    · exact nativeHeat072Fixed20_formula

theorem nativeHeatStep_chk_072_Gen :
    nativeHeatPassRootsOk nativeGap073Old nativeHeat072Frames nativeHeat072Coef nativeHeat072Fixed nativeHeat072Base 48 nativeHeat072Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_072_Gen : NativeHeatStepPassNum 72 := by
  refine nativeHeatStepPassNum_of_literals 72 nativeGap073Old nativeHeat072Frames (nativeHeatExpArg nativeGap073Old)
    nativeHeat072Exp nativeHeat072Coef nativeHeat072Fixed nativeHeat072Init nativeHeat072Base nativeHeatStep_hOld_072_Gen
    nativeHeatStep_hFr_072_Gen nativeHeatStep_hArg_072_Gen nativeHeatStep_hExp_072_Gen
    nativeHeatStep_hCoef_072_Gen nativeHeatStep_hFixed_072_Gen
    nativeHeatStep_hInit_072_Gen nativeHeatStep_hBase_072_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_072_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_072_Gen :
    nativeHeatY0Gen 72 = nativeShiftedFrame 1 (min nativeGap073Old.x nativeGap073Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_072_Gen, nativeHeatStep_hInd_072_Gen]

theorem nativeHeatStepFrameNum_072_Gen : NativeHeatStepFrameNum 72 := by
  have h1 := nativeHeatStep_hOld_072_Gen
  have h2 := nativeHeatStep_hInd_072_Gen
  have h3 := nativeHeatStep_hVar_072_Gen
  have h4 := nativeHeatStep_hQm_072_Gen
  have h5 := nativeHeatStep_hQN_072_Gen
  have h6 := nativeHeatStep_hY0_072_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_072_Gen : NativeHeatStepIndivNum 72 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 72 (by norm_num)) = nativeGap073Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_072_Gen]; exact nativeGap073Old_source
  · rw [hc, nativeHeatStep_hInd_072_Gen]; exact nativeGap073Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_072_Gen : nativeHeatY48Gen 72 = nativeHeat072Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_072_Gen, nativeHeatStep_hFr_072_Gen,
    nativeHeatStep_hCoef_072_Gen, nativeHeatStep_hFixed_072_Gen,
    nativeHeatStep_hBase_072_Gen]
  exact nativeHeat072All48

theorem nativeHeatResultGen_072 : nativeHeatResultGen 72 = nativeHeat072Result := by
  rw [← nativeHeat072Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_072_Gen, nativeHeatStep_hY0_072_Gen, nativeHeatStep_hExp_072_Gen,
    nativeHeatStep_hInit_072_Gen, nativeHeatStep_hFixed_072_Gen]

end ASDExplicitGamma.Native

end
