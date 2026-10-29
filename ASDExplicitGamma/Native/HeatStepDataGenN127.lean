module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat127Complete
public import ASDExplicitGamma.Numerics.Native.Gap128Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_127_Gen : nativeHeatOldRowGen 127 = nativeGap128Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_127_Gen : nativeHeatIndividualGen 127 = nativeGap128Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_127_Gen : nativeHeatGenVariance 127 = nativeHeat127Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_127_Gen, nativeHeat127Variance_formula]

theorem nativeHeatStep_hSpec_127_Gen : nativeHeatGenSpectral 127 = nativeHeat127Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_127_Gen, nativeHeat127Variance_formula]

theorem nativeHeatStep_hQm_127_Gen : nativeHeatGenQm 127 = nativeHeat127Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_127_Gen, nativeHeatStep_hSpec_127_Gen,
    nativeHeat127Qm_formula]

theorem nativeHeatStep_hQN_127_Gen : nativeHeatQNGen 127 = nativeHeat127QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_127_Gen, nativeHeat127QN_formula]

theorem nativeHeatStep_hFr_127_Gen : nativeHeatFramesGen 127 = nativeHeat127Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_127_Gen, nativeHeatStep_hInd_127_Gen,
    nativeHeatStep_hVar_127_Gen, nativeHeatStep_hQN_127_Gen, nativeHeat127Frames_formula]

theorem nativeHeatStep_hArg_127_Gen : nativeHeatExpArgGen 127 = nativeHeatExpArg nativeGap128Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_127_Gen]

theorem nativeHeatStep_hExp_127_Gen : nativeHeatExpGen 127 = nativeHeat127Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_127_Gen, nativeHeat127Exp_formula]

theorem nativeHeatStep_hCoef_127_Gen : nativeHeatCoefGen 127 = nativeHeat127Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_127_Gen, nativeHeat127Coef_formula]

theorem nativeHeatStep_hInit_127_Gen : nativeHeatInitGen 127 = nativeHeat127Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_127_Gen, nativeHeatStep_hVar_127_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat127Init00_formula
    · exact nativeHeat127Init01_formula
    · exact nativeHeat127Init02_formula
    · exact nativeHeat127Init03_formula
    · exact nativeHeat127Init04_formula
    · exact nativeHeat127Init05_formula
    · exact nativeHeat127Init06_formula
    · exact nativeHeat127Init07_formula
    · exact nativeHeat127Init08_formula
    · exact nativeHeat127Init09_formula
    · exact nativeHeat127Init10_formula
    · exact nativeHeat127Init11_formula
    · exact nativeHeat127Init12_formula
    · exact nativeHeat127Init13_formula
    · exact nativeHeat127Init14_formula
    · exact nativeHeat127Init15_formula
    · exact nativeHeat127Init16_formula
    · exact nativeHeat127Init17_formula
    · exact nativeHeat127Init18_formula
    · exact nativeHeat127Init19_formula
    · exact nativeHeat127Init20_formula
theorem nativeHeatStep_hBase_127_Gen : nativeHeatBaseGen 127 = nativeHeat127Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_127_Gen, nativeHeatStep_hInit_127_Gen, nativeHeat127Base_formula]

theorem nativeHeatStep_hFixed_127_Gen : nativeHeatFixedGen 127 = nativeHeat127Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_127_Gen, nativeHeatStep_hFr_127_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat127Fixed01_formula
    · exact nativeHeat127Fixed02_formula
    · exact nativeHeat127Fixed03_formula
    · exact nativeHeat127Fixed04_formula
    · exact nativeHeat127Fixed05_formula
    · exact nativeHeat127Fixed06_formula
    · exact nativeHeat127Fixed07_formula
    · exact nativeHeat127Fixed08_formula
    · exact nativeHeat127Fixed09_formula
    · exact nativeHeat127Fixed10_formula
    · exact nativeHeat127Fixed11_formula
    · exact nativeHeat127Fixed12_formula
    · exact nativeHeat127Fixed13_formula
    · exact nativeHeat127Fixed14_formula
    · exact nativeHeat127Fixed15_formula
    · exact nativeHeat127Fixed16_formula
    · exact nativeHeat127Fixed17_formula
    · exact nativeHeat127Fixed18_formula
    · exact nativeHeat127Fixed19_formula
    · exact nativeHeat127Fixed20_formula

theorem nativeHeatStep_chk_127_Gen :
    nativeHeatPassRootsOk nativeGap128Old nativeHeat127Frames nativeHeat127Coef nativeHeat127Fixed nativeHeat127Base 48 nativeHeat127Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_127_Gen : NativeHeatStepPassNum 127 := by
  refine nativeHeatStepPassNum_of_literals 127 nativeGap128Old nativeHeat127Frames (nativeHeatExpArg nativeGap128Old)
    nativeHeat127Exp nativeHeat127Coef nativeHeat127Fixed nativeHeat127Init nativeHeat127Base nativeHeatStep_hOld_127_Gen
    nativeHeatStep_hFr_127_Gen nativeHeatStep_hArg_127_Gen nativeHeatStep_hExp_127_Gen
    nativeHeatStep_hCoef_127_Gen nativeHeatStep_hFixed_127_Gen
    nativeHeatStep_hInit_127_Gen nativeHeatStep_hBase_127_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_127_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_127_Gen :
    nativeHeatY0Gen 127 = nativeShiftedFrame 1 (min nativeGap128Old.x nativeGap128Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_127_Gen, nativeHeatStep_hInd_127_Gen]

theorem nativeHeatStepFrameNum_127_Gen : NativeHeatStepFrameNum 127 := by
  have h1 := nativeHeatStep_hOld_127_Gen
  have h2 := nativeHeatStep_hInd_127_Gen
  have h3 := nativeHeatStep_hVar_127_Gen
  have h4 := nativeHeatStep_hQm_127_Gen
  have h5 := nativeHeatStep_hQN_127_Gen
  have h6 := nativeHeatStep_hY0_127_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_127_Gen : NativeHeatStepIndivNum 127 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 127 (by norm_num)) = nativeGap128Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_127_Gen]; exact nativeGap128Old_source
  · rw [hc, nativeHeatStep_hInd_127_Gen]; exact nativeGap128Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_127_Gen : nativeHeatY48Gen 127 = nativeHeat127Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_127_Gen, nativeHeatStep_hFr_127_Gen,
    nativeHeatStep_hCoef_127_Gen, nativeHeatStep_hFixed_127_Gen,
    nativeHeatStep_hBase_127_Gen]
  exact nativeHeat127All48

theorem nativeHeatResultGen_127 : nativeHeatResultGen 127 = nativeHeat127Result := by
  rw [← nativeHeat127Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_127_Gen, nativeHeatStep_hY0_127_Gen, nativeHeatStep_hExp_127_Gen,
    nativeHeatStep_hInit_127_Gen, nativeHeatStep_hFixed_127_Gen]

end ASDExplicitGamma.Native

end
