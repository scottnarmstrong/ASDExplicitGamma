module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat129Complete
public import ASDExplicitGamma.Numerics.Native.Gap130Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_129_Gen : nativeHeatOldRowGen 129 = nativeGap130Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_129_Gen : nativeHeatIndividualGen 129 = nativeGap130Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_129_Gen : nativeHeatGenVariance 129 = nativeHeat129Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_129_Gen, nativeHeat129Variance_formula]

theorem nativeHeatStep_hSpec_129_Gen : nativeHeatGenSpectral 129 = nativeHeat129Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_129_Gen, nativeHeat129Variance_formula]

theorem nativeHeatStep_hQm_129_Gen : nativeHeatGenQm 129 = nativeHeat129Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_129_Gen, nativeHeatStep_hSpec_129_Gen,
    nativeHeat129Qm_formula]

theorem nativeHeatStep_hQN_129_Gen : nativeHeatQNGen 129 = nativeHeat129QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_129_Gen, nativeHeat129QN_formula]

theorem nativeHeatStep_hFr_129_Gen : nativeHeatFramesGen 129 = nativeHeat129Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_129_Gen, nativeHeatStep_hInd_129_Gen,
    nativeHeatStep_hVar_129_Gen, nativeHeatStep_hQN_129_Gen, nativeHeat129Frames_formula]

theorem nativeHeatStep_hArg_129_Gen : nativeHeatExpArgGen 129 = nativeHeatExpArg nativeGap130Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_129_Gen]

theorem nativeHeatStep_hExp_129_Gen : nativeHeatExpGen 129 = nativeHeat129Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_129_Gen, nativeHeat129Exp_formula]

theorem nativeHeatStep_hCoef_129_Gen : nativeHeatCoefGen 129 = nativeHeat129Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_129_Gen, nativeHeat129Coef_formula]

theorem nativeHeatStep_hInit_129_Gen : nativeHeatInitGen 129 = nativeHeat129Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_129_Gen, nativeHeatStep_hVar_129_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat129Init00_formula
    · exact nativeHeat129Init01_formula
    · exact nativeHeat129Init02_formula
    · exact nativeHeat129Init03_formula
    · exact nativeHeat129Init04_formula
    · exact nativeHeat129Init05_formula
    · exact nativeHeat129Init06_formula
    · exact nativeHeat129Init07_formula
    · exact nativeHeat129Init08_formula
    · exact nativeHeat129Init09_formula
    · exact nativeHeat129Init10_formula
    · exact nativeHeat129Init11_formula
    · exact nativeHeat129Init12_formula
    · exact nativeHeat129Init13_formula
    · exact nativeHeat129Init14_formula
    · exact nativeHeat129Init15_formula
    · exact nativeHeat129Init16_formula
    · exact nativeHeat129Init17_formula
    · exact nativeHeat129Init18_formula
    · exact nativeHeat129Init19_formula
    · exact nativeHeat129Init20_formula
theorem nativeHeatStep_hBase_129_Gen : nativeHeatBaseGen 129 = nativeHeat129Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_129_Gen, nativeHeatStep_hInit_129_Gen, nativeHeat129Base_formula]

theorem nativeHeatStep_hFixed_129_Gen : nativeHeatFixedGen 129 = nativeHeat129Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_129_Gen, nativeHeatStep_hFr_129_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat129Fixed01_formula
    · exact nativeHeat129Fixed02_formula
    · exact nativeHeat129Fixed03_formula
    · exact nativeHeat129Fixed04_formula
    · exact nativeHeat129Fixed05_formula
    · exact nativeHeat129Fixed06_formula
    · exact nativeHeat129Fixed07_formula
    · exact nativeHeat129Fixed08_formula
    · exact nativeHeat129Fixed09_formula
    · exact nativeHeat129Fixed10_formula
    · exact nativeHeat129Fixed11_formula
    · exact nativeHeat129Fixed12_formula
    · exact nativeHeat129Fixed13_formula
    · exact nativeHeat129Fixed14_formula
    · exact nativeHeat129Fixed15_formula
    · exact nativeHeat129Fixed16_formula
    · exact nativeHeat129Fixed17_formula
    · exact nativeHeat129Fixed18_formula
    · exact nativeHeat129Fixed19_formula
    · exact nativeHeat129Fixed20_formula

theorem nativeHeatStep_chk_129_Gen :
    nativeHeatPassRootsOk nativeGap130Old nativeHeat129Frames nativeHeat129Coef nativeHeat129Fixed nativeHeat129Base 48 nativeHeat129Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_129_Gen : NativeHeatStepPassNum 129 := by
  refine nativeHeatStepPassNum_of_literals 129 nativeGap130Old nativeHeat129Frames (nativeHeatExpArg nativeGap130Old)
    nativeHeat129Exp nativeHeat129Coef nativeHeat129Fixed nativeHeat129Init nativeHeat129Base nativeHeatStep_hOld_129_Gen
    nativeHeatStep_hFr_129_Gen nativeHeatStep_hArg_129_Gen nativeHeatStep_hExp_129_Gen
    nativeHeatStep_hCoef_129_Gen nativeHeatStep_hFixed_129_Gen
    nativeHeatStep_hInit_129_Gen nativeHeatStep_hBase_129_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_129_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_129_Gen :
    nativeHeatY0Gen 129 = nativeShiftedFrame 1 (min nativeGap130Old.x nativeGap130Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_129_Gen, nativeHeatStep_hInd_129_Gen]

theorem nativeHeatStepFrameNum_129_Gen : NativeHeatStepFrameNum 129 := by
  have h1 := nativeHeatStep_hOld_129_Gen
  have h2 := nativeHeatStep_hInd_129_Gen
  have h3 := nativeHeatStep_hVar_129_Gen
  have h4 := nativeHeatStep_hQm_129_Gen
  have h5 := nativeHeatStep_hQN_129_Gen
  have h6 := nativeHeatStep_hY0_129_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_129_Gen : NativeHeatStepIndivNum 129 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 129 (by norm_num)) = nativeGap130Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_129_Gen]; exact nativeGap130Old_source
  · rw [hc, nativeHeatStep_hInd_129_Gen]; exact nativeGap130Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_129_Gen : nativeHeatY48Gen 129 = nativeHeat129Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_129_Gen, nativeHeatStep_hFr_129_Gen,
    nativeHeatStep_hCoef_129_Gen, nativeHeatStep_hFixed_129_Gen,
    nativeHeatStep_hBase_129_Gen]
  exact nativeHeat129All48

theorem nativeHeatResultGen_129 : nativeHeatResultGen 129 = nativeHeat129Result := by
  rw [← nativeHeat129Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_129_Gen, nativeHeatStep_hY0_129_Gen, nativeHeatStep_hExp_129_Gen,
    nativeHeatStep_hInit_129_Gen, nativeHeatStep_hFixed_129_Gen]

end ASDExplicitGamma.Native

end
