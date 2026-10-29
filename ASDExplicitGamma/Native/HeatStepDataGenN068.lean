module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat068Complete
public import ASDExplicitGamma.Numerics.Native.Gap069Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_068_Gen : nativeHeatOldRowGen 68 = nativeGap069Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_068_Gen : nativeHeatIndividualGen 68 = nativeGap069Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_068_Gen : nativeHeatGenVariance 68 = nativeHeat068Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_068_Gen, nativeHeat068Variance_formula]

theorem nativeHeatStep_hSpec_068_Gen : nativeHeatGenSpectral 68 = nativeHeat068Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_068_Gen, nativeHeat068Variance_formula]

theorem nativeHeatStep_hQm_068_Gen : nativeHeatGenQm 68 = nativeHeat068Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_068_Gen, nativeHeatStep_hSpec_068_Gen,
    nativeHeat068Qm_formula]

theorem nativeHeatStep_hQN_068_Gen : nativeHeatQNGen 68 = nativeHeat068QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_068_Gen, nativeHeat068QN_formula]

theorem nativeHeatStep_hFr_068_Gen : nativeHeatFramesGen 68 = nativeHeat068Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_068_Gen, nativeHeatStep_hInd_068_Gen,
    nativeHeatStep_hVar_068_Gen, nativeHeatStep_hQN_068_Gen, nativeHeat068Frames_formula]

theorem nativeHeatStep_hArg_068_Gen : nativeHeatExpArgGen 68 = nativeHeatExpArg nativeGap069Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_068_Gen]

theorem nativeHeatStep_hExp_068_Gen : nativeHeatExpGen 68 = nativeHeat068Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_068_Gen, nativeHeat068Exp_formula]

theorem nativeHeatStep_hCoef_068_Gen : nativeHeatCoefGen 68 = nativeHeat068Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_068_Gen, nativeHeat068Coef_formula]

theorem nativeHeatStep_hInit_068_Gen : nativeHeatInitGen 68 = nativeHeat068Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_068_Gen, nativeHeatStep_hVar_068_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat068Init00_formula
    · exact nativeHeat068Init01_formula
    · exact nativeHeat068Init02_formula
    · exact nativeHeat068Init03_formula
    · exact nativeHeat068Init04_formula
    · exact nativeHeat068Init05_formula
    · exact nativeHeat068Init06_formula
    · exact nativeHeat068Init07_formula
    · exact nativeHeat068Init08_formula
    · exact nativeHeat068Init09_formula
    · exact nativeHeat068Init10_formula
    · exact nativeHeat068Init11_formula
    · exact nativeHeat068Init12_formula
    · exact nativeHeat068Init13_formula
    · exact nativeHeat068Init14_formula
    · exact nativeHeat068Init15_formula
    · exact nativeHeat068Init16_formula
    · exact nativeHeat068Init17_formula
    · exact nativeHeat068Init18_formula
    · exact nativeHeat068Init19_formula
    · exact nativeHeat068Init20_formula
theorem nativeHeatStep_hBase_068_Gen : nativeHeatBaseGen 68 = nativeHeat068Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_068_Gen, nativeHeatStep_hInit_068_Gen, nativeHeat068Base_formula]

theorem nativeHeatStep_hFixed_068_Gen : nativeHeatFixedGen 68 = nativeHeat068Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_068_Gen, nativeHeatStep_hFr_068_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat068Fixed01_formula
    · exact nativeHeat068Fixed02_formula
    · exact nativeHeat068Fixed03_formula
    · exact nativeHeat068Fixed04_formula
    · exact nativeHeat068Fixed05_formula
    · exact nativeHeat068Fixed06_formula
    · exact nativeHeat068Fixed07_formula
    · exact nativeHeat068Fixed08_formula
    · exact nativeHeat068Fixed09_formula
    · exact nativeHeat068Fixed10_formula
    · exact nativeHeat068Fixed11_formula
    · exact nativeHeat068Fixed12_formula
    · exact nativeHeat068Fixed13_formula
    · exact nativeHeat068Fixed14_formula
    · exact nativeHeat068Fixed15_formula
    · exact nativeHeat068Fixed16_formula
    · exact nativeHeat068Fixed17_formula
    · exact nativeHeat068Fixed18_formula
    · exact nativeHeat068Fixed19_formula
    · exact nativeHeat068Fixed20_formula

theorem nativeHeatStep_chk_068_Gen :
    nativeHeatPassRootsOk nativeGap069Old nativeHeat068Frames nativeHeat068Coef nativeHeat068Fixed nativeHeat068Base 48 nativeHeat068Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_068_Gen : NativeHeatStepPassNum 68 := by
  refine nativeHeatStepPassNum_of_literals 68 nativeGap069Old nativeHeat068Frames (nativeHeatExpArg nativeGap069Old)
    nativeHeat068Exp nativeHeat068Coef nativeHeat068Fixed nativeHeat068Init nativeHeat068Base nativeHeatStep_hOld_068_Gen
    nativeHeatStep_hFr_068_Gen nativeHeatStep_hArg_068_Gen nativeHeatStep_hExp_068_Gen
    nativeHeatStep_hCoef_068_Gen nativeHeatStep_hFixed_068_Gen
    nativeHeatStep_hInit_068_Gen nativeHeatStep_hBase_068_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_068_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_068_Gen :
    nativeHeatY0Gen 68 = nativeShiftedFrame 1 (min nativeGap069Old.x nativeGap069Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_068_Gen, nativeHeatStep_hInd_068_Gen]

theorem nativeHeatStepFrameNum_068_Gen : NativeHeatStepFrameNum 68 := by
  have h1 := nativeHeatStep_hOld_068_Gen
  have h2 := nativeHeatStep_hInd_068_Gen
  have h3 := nativeHeatStep_hVar_068_Gen
  have h4 := nativeHeatStep_hQm_068_Gen
  have h5 := nativeHeatStep_hQN_068_Gen
  have h6 := nativeHeatStep_hY0_068_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_068_Gen : NativeHeatStepIndivNum 68 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 68 (by norm_num)) = nativeGap069Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_068_Gen]; exact nativeGap069Old_source
  · rw [hc, nativeHeatStep_hInd_068_Gen]; exact nativeGap069Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_068_Gen : nativeHeatY48Gen 68 = nativeHeat068Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_068_Gen, nativeHeatStep_hFr_068_Gen,
    nativeHeatStep_hCoef_068_Gen, nativeHeatStep_hFixed_068_Gen,
    nativeHeatStep_hBase_068_Gen]
  exact nativeHeat068All48

theorem nativeHeatResultGen_068 : nativeHeatResultGen 68 = nativeHeat068Result := by
  rw [← nativeHeat068Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_068_Gen, nativeHeatStep_hY0_068_Gen, nativeHeatStep_hExp_068_Gen,
    nativeHeatStep_hInit_068_Gen, nativeHeatStep_hFixed_068_Gen]

end ASDExplicitGamma.Native

end
