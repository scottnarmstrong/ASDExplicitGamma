module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat110Complete
public import ASDExplicitGamma.Numerics.Native.Gap111Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_110_Gen : nativeHeatOldRowGen 110 = nativeGap111Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_110_Gen : nativeHeatIndividualGen 110 = nativeGap111Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_110_Gen : nativeHeatGenVariance 110 = nativeHeat110Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_110_Gen, nativeHeat110Variance_formula]

theorem nativeHeatStep_hSpec_110_Gen : nativeHeatGenSpectral 110 = nativeHeat110Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_110_Gen, nativeHeat110Variance_formula]

theorem nativeHeatStep_hQm_110_Gen : nativeHeatGenQm 110 = nativeHeat110Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_110_Gen, nativeHeatStep_hSpec_110_Gen,
    nativeHeat110Qm_formula]

theorem nativeHeatStep_hQN_110_Gen : nativeHeatQNGen 110 = nativeHeat110QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_110_Gen, nativeHeat110QN_formula]

theorem nativeHeatStep_hFr_110_Gen : nativeHeatFramesGen 110 = nativeHeat110Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_110_Gen, nativeHeatStep_hInd_110_Gen,
    nativeHeatStep_hVar_110_Gen, nativeHeatStep_hQN_110_Gen, nativeHeat110Frames_formula]

theorem nativeHeatStep_hArg_110_Gen : nativeHeatExpArgGen 110 = nativeHeatExpArg nativeGap111Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_110_Gen]

theorem nativeHeatStep_hExp_110_Gen : nativeHeatExpGen 110 = nativeHeat110Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_110_Gen, nativeHeat110Exp_formula]

theorem nativeHeatStep_hCoef_110_Gen : nativeHeatCoefGen 110 = nativeHeat110Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_110_Gen, nativeHeat110Coef_formula]

theorem nativeHeatStep_hInit_110_Gen : nativeHeatInitGen 110 = nativeHeat110Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_110_Gen, nativeHeatStep_hVar_110_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat110Init00_formula
    · exact nativeHeat110Init01_formula
    · exact nativeHeat110Init02_formula
    · exact nativeHeat110Init03_formula
    · exact nativeHeat110Init04_formula
    · exact nativeHeat110Init05_formula
    · exact nativeHeat110Init06_formula
    · exact nativeHeat110Init07_formula
    · exact nativeHeat110Init08_formula
    · exact nativeHeat110Init09_formula
    · exact nativeHeat110Init10_formula
    · exact nativeHeat110Init11_formula
    · exact nativeHeat110Init12_formula
    · exact nativeHeat110Init13_formula
    · exact nativeHeat110Init14_formula
    · exact nativeHeat110Init15_formula
    · exact nativeHeat110Init16_formula
    · exact nativeHeat110Init17_formula
    · exact nativeHeat110Init18_formula
    · exact nativeHeat110Init19_formula
    · exact nativeHeat110Init20_formula
theorem nativeHeatStep_hBase_110_Gen : nativeHeatBaseGen 110 = nativeHeat110Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_110_Gen, nativeHeatStep_hInit_110_Gen, nativeHeat110Base_formula]

theorem nativeHeatStep_hFixed_110_Gen : nativeHeatFixedGen 110 = nativeHeat110Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_110_Gen, nativeHeatStep_hFr_110_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat110Fixed01_formula
    · exact nativeHeat110Fixed02_formula
    · exact nativeHeat110Fixed03_formula
    · exact nativeHeat110Fixed04_formula
    · exact nativeHeat110Fixed05_formula
    · exact nativeHeat110Fixed06_formula
    · exact nativeHeat110Fixed07_formula
    · exact nativeHeat110Fixed08_formula
    · exact nativeHeat110Fixed09_formula
    · exact nativeHeat110Fixed10_formula
    · exact nativeHeat110Fixed11_formula
    · exact nativeHeat110Fixed12_formula
    · exact nativeHeat110Fixed13_formula
    · exact nativeHeat110Fixed14_formula
    · exact nativeHeat110Fixed15_formula
    · exact nativeHeat110Fixed16_formula
    · exact nativeHeat110Fixed17_formula
    · exact nativeHeat110Fixed18_formula
    · exact nativeHeat110Fixed19_formula
    · exact nativeHeat110Fixed20_formula

theorem nativeHeatStep_chk_110_Gen :
    nativeHeatPassRootsOk nativeGap111Old nativeHeat110Frames nativeHeat110Coef nativeHeat110Fixed nativeHeat110Base 48 nativeHeat110Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_110_Gen : NativeHeatStepPassNum 110 := by
  refine nativeHeatStepPassNum_of_literals 110 nativeGap111Old nativeHeat110Frames (nativeHeatExpArg nativeGap111Old)
    nativeHeat110Exp nativeHeat110Coef nativeHeat110Fixed nativeHeat110Init nativeHeat110Base nativeHeatStep_hOld_110_Gen
    nativeHeatStep_hFr_110_Gen nativeHeatStep_hArg_110_Gen nativeHeatStep_hExp_110_Gen
    nativeHeatStep_hCoef_110_Gen nativeHeatStep_hFixed_110_Gen
    nativeHeatStep_hInit_110_Gen nativeHeatStep_hBase_110_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_110_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_110_Gen :
    nativeHeatY0Gen 110 = nativeShiftedFrame 1 (min nativeGap111Old.x nativeGap111Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_110_Gen, nativeHeatStep_hInd_110_Gen]

theorem nativeHeatStepFrameNum_110_Gen : NativeHeatStepFrameNum 110 := by
  have h1 := nativeHeatStep_hOld_110_Gen
  have h2 := nativeHeatStep_hInd_110_Gen
  have h3 := nativeHeatStep_hVar_110_Gen
  have h4 := nativeHeatStep_hQm_110_Gen
  have h5 := nativeHeatStep_hQN_110_Gen
  have h6 := nativeHeatStep_hY0_110_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_110_Gen : NativeHeatStepIndivNum 110 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 110 (by norm_num)) = nativeGap111Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_110_Gen]; exact nativeGap111Old_source
  · rw [hc, nativeHeatStep_hInd_110_Gen]; exact nativeGap111Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_110_Gen : nativeHeatY48Gen 110 = nativeHeat110Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_110_Gen, nativeHeatStep_hFr_110_Gen,
    nativeHeatStep_hCoef_110_Gen, nativeHeatStep_hFixed_110_Gen,
    nativeHeatStep_hBase_110_Gen]
  exact nativeHeat110All48

theorem nativeHeatResultGen_110 : nativeHeatResultGen 110 = nativeHeat110Result := by
  rw [← nativeHeat110Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_110_Gen, nativeHeatStep_hY0_110_Gen, nativeHeatStep_hExp_110_Gen,
    nativeHeatStep_hInit_110_Gen, nativeHeatStep_hFixed_110_Gen]

end ASDExplicitGamma.Native

end
