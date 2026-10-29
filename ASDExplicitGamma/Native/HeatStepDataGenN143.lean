module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat143Complete
public import ASDExplicitGamma.Numerics.Native.Gap144Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_143_Gen : nativeHeatOldRowGen 143 = nativeGap144Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_143_Gen : nativeHeatIndividualGen 143 = nativeGap144Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_143_Gen : nativeHeatGenVariance 143 = nativeHeat143Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_143_Gen, nativeHeat143Variance_formula]

theorem nativeHeatStep_hSpec_143_Gen : nativeHeatGenSpectral 143 = nativeHeat143Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_143_Gen, nativeHeat143Variance_formula]

theorem nativeHeatStep_hQm_143_Gen : nativeHeatGenQm 143 = nativeHeat143Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_143_Gen, nativeHeatStep_hSpec_143_Gen,
    nativeHeat143Qm_formula]

theorem nativeHeatStep_hQN_143_Gen : nativeHeatQNGen 143 = nativeHeat143QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_143_Gen, nativeHeat143QN_formula]

theorem nativeHeatStep_hFr_143_Gen : nativeHeatFramesGen 143 = nativeHeat143Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_143_Gen, nativeHeatStep_hInd_143_Gen,
    nativeHeatStep_hVar_143_Gen, nativeHeatStep_hQN_143_Gen, nativeHeat143Frames_formula]

theorem nativeHeatStep_hArg_143_Gen : nativeHeatExpArgGen 143 = nativeHeatExpArg nativeGap144Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_143_Gen]

theorem nativeHeatStep_hExp_143_Gen : nativeHeatExpGen 143 = nativeHeat143Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_143_Gen, nativeHeat143Exp_formula]

theorem nativeHeatStep_hCoef_143_Gen : nativeHeatCoefGen 143 = nativeHeat143Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_143_Gen, nativeHeat143Coef_formula]

theorem nativeHeatStep_hInit_143_Gen : nativeHeatInitGen 143 = nativeHeat143Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_143_Gen, nativeHeatStep_hVar_143_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat143Init00_formula
    · exact nativeHeat143Init01_formula
    · exact nativeHeat143Init02_formula
    · exact nativeHeat143Init03_formula
    · exact nativeHeat143Init04_formula
    · exact nativeHeat143Init05_formula
    · exact nativeHeat143Init06_formula
    · exact nativeHeat143Init07_formula
    · exact nativeHeat143Init08_formula
    · exact nativeHeat143Init09_formula
    · exact nativeHeat143Init10_formula
    · exact nativeHeat143Init11_formula
    · exact nativeHeat143Init12_formula
    · exact nativeHeat143Init13_formula
    · exact nativeHeat143Init14_formula
    · exact nativeHeat143Init15_formula
    · exact nativeHeat143Init16_formula
    · exact nativeHeat143Init17_formula
    · exact nativeHeat143Init18_formula
    · exact nativeHeat143Init19_formula
    · exact nativeHeat143Init20_formula
theorem nativeHeatStep_hBase_143_Gen : nativeHeatBaseGen 143 = nativeHeat143Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_143_Gen, nativeHeatStep_hInit_143_Gen, nativeHeat143Base_formula]

theorem nativeHeatStep_hFixed_143_Gen : nativeHeatFixedGen 143 = nativeHeat143Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_143_Gen, nativeHeatStep_hFr_143_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat143Fixed01_formula
    · exact nativeHeat143Fixed02_formula
    · exact nativeHeat143Fixed03_formula
    · exact nativeHeat143Fixed04_formula
    · exact nativeHeat143Fixed05_formula
    · exact nativeHeat143Fixed06_formula
    · exact nativeHeat143Fixed07_formula
    · exact nativeHeat143Fixed08_formula
    · exact nativeHeat143Fixed09_formula
    · exact nativeHeat143Fixed10_formula
    · exact nativeHeat143Fixed11_formula
    · exact nativeHeat143Fixed12_formula
    · exact nativeHeat143Fixed13_formula
    · exact nativeHeat143Fixed14_formula
    · exact nativeHeat143Fixed15_formula
    · exact nativeHeat143Fixed16_formula
    · exact nativeHeat143Fixed17_formula
    · exact nativeHeat143Fixed18_formula
    · exact nativeHeat143Fixed19_formula
    · exact nativeHeat143Fixed20_formula

theorem nativeHeatStep_chk_143_Gen :
    nativeHeatPassRootsOk nativeGap144Old nativeHeat143Frames nativeHeat143Coef nativeHeat143Fixed nativeHeat143Base 48 nativeHeat143Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_143_Gen : NativeHeatStepPassNum 143 := by
  refine nativeHeatStepPassNum_of_literals 143 nativeGap144Old nativeHeat143Frames (nativeHeatExpArg nativeGap144Old)
    nativeHeat143Exp nativeHeat143Coef nativeHeat143Fixed nativeHeat143Init nativeHeat143Base nativeHeatStep_hOld_143_Gen
    nativeHeatStep_hFr_143_Gen nativeHeatStep_hArg_143_Gen nativeHeatStep_hExp_143_Gen
    nativeHeatStep_hCoef_143_Gen nativeHeatStep_hFixed_143_Gen
    nativeHeatStep_hInit_143_Gen nativeHeatStep_hBase_143_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_143_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_143_Gen :
    nativeHeatY0Gen 143 = nativeShiftedFrame 1 (min nativeGap144Old.x nativeGap144Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_143_Gen, nativeHeatStep_hInd_143_Gen]

theorem nativeHeatStepFrameNum_143_Gen : NativeHeatStepFrameNum 143 := by
  have h1 := nativeHeatStep_hOld_143_Gen
  have h2 := nativeHeatStep_hInd_143_Gen
  have h3 := nativeHeatStep_hVar_143_Gen
  have h4 := nativeHeatStep_hQm_143_Gen
  have h5 := nativeHeatStep_hQN_143_Gen
  have h6 := nativeHeatStep_hY0_143_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_143_Gen : NativeHeatStepIndivNum 143 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 143 (by norm_num)) = nativeGap144Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_143_Gen]; exact nativeGap144Old_source
  · rw [hc, nativeHeatStep_hInd_143_Gen]; exact nativeGap144Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_143_Gen : nativeHeatY48Gen 143 = nativeHeat143Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_143_Gen, nativeHeatStep_hFr_143_Gen,
    nativeHeatStep_hCoef_143_Gen, nativeHeatStep_hFixed_143_Gen,
    nativeHeatStep_hBase_143_Gen]
  exact nativeHeat143All48

theorem nativeHeatResultGen_143 : nativeHeatResultGen 143 = nativeHeat143Result := by
  rw [← nativeHeat143Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_143_Gen, nativeHeatStep_hY0_143_Gen, nativeHeatStep_hExp_143_Gen,
    nativeHeatStep_hInit_143_Gen, nativeHeatStep_hFixed_143_Gen]

end ASDExplicitGamma.Native

end
