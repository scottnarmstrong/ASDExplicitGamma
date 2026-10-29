module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat144Complete
public import ASDExplicitGamma.Numerics.Native.Gap145Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_144_Gen : nativeHeatOldRowGen 144 = nativeGap145Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_144_Gen : nativeHeatIndividualGen 144 = nativeGap145Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_144_Gen : nativeHeatGenVariance 144 = nativeHeat144Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_144_Gen, nativeHeat144Variance_formula]

theorem nativeHeatStep_hSpec_144_Gen : nativeHeatGenSpectral 144 = nativeHeat144Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_144_Gen, nativeHeat144Variance_formula]

theorem nativeHeatStep_hQm_144_Gen : nativeHeatGenQm 144 = nativeHeat144Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_144_Gen, nativeHeatStep_hSpec_144_Gen,
    nativeHeat144Qm_formula]

theorem nativeHeatStep_hQN_144_Gen : nativeHeatQNGen 144 = nativeHeat144QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_144_Gen, nativeHeat144QN_formula]

theorem nativeHeatStep_hFr_144_Gen : nativeHeatFramesGen 144 = nativeHeat144Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_144_Gen, nativeHeatStep_hInd_144_Gen,
    nativeHeatStep_hVar_144_Gen, nativeHeatStep_hQN_144_Gen, nativeHeat144Frames_formula]

theorem nativeHeatStep_hArg_144_Gen : nativeHeatExpArgGen 144 = nativeHeatExpArg nativeGap145Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_144_Gen]

theorem nativeHeatStep_hExp_144_Gen : nativeHeatExpGen 144 = nativeHeat144Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_144_Gen, nativeHeat144Exp_formula]

theorem nativeHeatStep_hCoef_144_Gen : nativeHeatCoefGen 144 = nativeHeat144Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_144_Gen, nativeHeat144Coef_formula]

theorem nativeHeatStep_hInit_144_Gen : nativeHeatInitGen 144 = nativeHeat144Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_144_Gen, nativeHeatStep_hVar_144_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat144Init00_formula
    · exact nativeHeat144Init01_formula
    · exact nativeHeat144Init02_formula
    · exact nativeHeat144Init03_formula
    · exact nativeHeat144Init04_formula
    · exact nativeHeat144Init05_formula
    · exact nativeHeat144Init06_formula
    · exact nativeHeat144Init07_formula
    · exact nativeHeat144Init08_formula
    · exact nativeHeat144Init09_formula
    · exact nativeHeat144Init10_formula
    · exact nativeHeat144Init11_formula
    · exact nativeHeat144Init12_formula
    · exact nativeHeat144Init13_formula
    · exact nativeHeat144Init14_formula
    · exact nativeHeat144Init15_formula
    · exact nativeHeat144Init16_formula
    · exact nativeHeat144Init17_formula
    · exact nativeHeat144Init18_formula
    · exact nativeHeat144Init19_formula
    · exact nativeHeat144Init20_formula
theorem nativeHeatStep_hBase_144_Gen : nativeHeatBaseGen 144 = nativeHeat144Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_144_Gen, nativeHeatStep_hInit_144_Gen, nativeHeat144Base_formula]

theorem nativeHeatStep_hFixed_144_Gen : nativeHeatFixedGen 144 = nativeHeat144Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_144_Gen, nativeHeatStep_hFr_144_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat144Fixed01_formula
    · exact nativeHeat144Fixed02_formula
    · exact nativeHeat144Fixed03_formula
    · exact nativeHeat144Fixed04_formula
    · exact nativeHeat144Fixed05_formula
    · exact nativeHeat144Fixed06_formula
    · exact nativeHeat144Fixed07_formula
    · exact nativeHeat144Fixed08_formula
    · exact nativeHeat144Fixed09_formula
    · exact nativeHeat144Fixed10_formula
    · exact nativeHeat144Fixed11_formula
    · exact nativeHeat144Fixed12_formula
    · exact nativeHeat144Fixed13_formula
    · exact nativeHeat144Fixed14_formula
    · exact nativeHeat144Fixed15_formula
    · exact nativeHeat144Fixed16_formula
    · exact nativeHeat144Fixed17_formula
    · exact nativeHeat144Fixed18_formula
    · exact nativeHeat144Fixed19_formula
    · exact nativeHeat144Fixed20_formula

theorem nativeHeatStep_chk_144_Gen :
    nativeHeatPassRootsOk nativeGap145Old nativeHeat144Frames nativeHeat144Coef nativeHeat144Fixed nativeHeat144Base 48 nativeHeat144Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_144_Gen : NativeHeatStepPassNum 144 := by
  refine nativeHeatStepPassNum_of_literals 144 nativeGap145Old nativeHeat144Frames (nativeHeatExpArg nativeGap145Old)
    nativeHeat144Exp nativeHeat144Coef nativeHeat144Fixed nativeHeat144Init nativeHeat144Base nativeHeatStep_hOld_144_Gen
    nativeHeatStep_hFr_144_Gen nativeHeatStep_hArg_144_Gen nativeHeatStep_hExp_144_Gen
    nativeHeatStep_hCoef_144_Gen nativeHeatStep_hFixed_144_Gen
    nativeHeatStep_hInit_144_Gen nativeHeatStep_hBase_144_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_144_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_144_Gen :
    nativeHeatY0Gen 144 = nativeShiftedFrame 1 (min nativeGap145Old.x nativeGap145Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_144_Gen, nativeHeatStep_hInd_144_Gen]

theorem nativeHeatStepFrameNum_144_Gen : NativeHeatStepFrameNum 144 := by
  have h1 := nativeHeatStep_hOld_144_Gen
  have h2 := nativeHeatStep_hInd_144_Gen
  have h3 := nativeHeatStep_hVar_144_Gen
  have h4 := nativeHeatStep_hQm_144_Gen
  have h5 := nativeHeatStep_hQN_144_Gen
  have h6 := nativeHeatStep_hY0_144_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_144_Gen : NativeHeatStepIndivNum 144 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 144 (by norm_num)) = nativeGap145Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_144_Gen]; exact nativeGap145Old_source
  · rw [hc, nativeHeatStep_hInd_144_Gen]; exact nativeGap145Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_144_Gen : nativeHeatY48Gen 144 = nativeHeat144Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_144_Gen, nativeHeatStep_hFr_144_Gen,
    nativeHeatStep_hCoef_144_Gen, nativeHeatStep_hFixed_144_Gen,
    nativeHeatStep_hBase_144_Gen]
  exact nativeHeat144All48

theorem nativeHeatResultGen_144 : nativeHeatResultGen 144 = nativeHeat144Result := by
  rw [← nativeHeat144Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_144_Gen, nativeHeatStep_hY0_144_Gen, nativeHeatStep_hExp_144_Gen,
    nativeHeatStep_hInit_144_Gen, nativeHeatStep_hFixed_144_Gen]

end ASDExplicitGamma.Native

end
