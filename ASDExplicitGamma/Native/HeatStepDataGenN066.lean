module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat066Complete
public import ASDExplicitGamma.Numerics.Native.Gap067Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_066_Gen : nativeHeatOldRowGen 66 = nativeGap067Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_066_Gen : nativeHeatIndividualGen 66 = nativeGap067Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_066_Gen : nativeHeatGenVariance 66 = nativeHeat066Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_066_Gen, nativeHeat066Variance_formula]

theorem nativeHeatStep_hSpec_066_Gen : nativeHeatGenSpectral 66 = nativeHeat066Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_066_Gen, nativeHeat066Variance_formula]

theorem nativeHeatStep_hQm_066_Gen : nativeHeatGenQm 66 = nativeHeat066Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_066_Gen, nativeHeatStep_hSpec_066_Gen,
    nativeHeat066Qm_formula]

theorem nativeHeatStep_hQN_066_Gen : nativeHeatQNGen 66 = nativeHeat066QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_066_Gen, nativeHeat066QN_formula]

theorem nativeHeatStep_hFr_066_Gen : nativeHeatFramesGen 66 = nativeHeat066Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_066_Gen, nativeHeatStep_hInd_066_Gen,
    nativeHeatStep_hVar_066_Gen, nativeHeatStep_hQN_066_Gen, nativeHeat066Frames_formula]

theorem nativeHeatStep_hArg_066_Gen : nativeHeatExpArgGen 66 = nativeHeatExpArg nativeGap067Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_066_Gen]

theorem nativeHeatStep_hExp_066_Gen : nativeHeatExpGen 66 = nativeHeat066Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_066_Gen, nativeHeat066Exp_formula]

theorem nativeHeatStep_hCoef_066_Gen : nativeHeatCoefGen 66 = nativeHeat066Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_066_Gen, nativeHeat066Coef_formula]

theorem nativeHeatStep_hInit_066_Gen : nativeHeatInitGen 66 = nativeHeat066Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_066_Gen, nativeHeatStep_hVar_066_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat066Init00_formula
    · exact nativeHeat066Init01_formula
    · exact nativeHeat066Init02_formula
    · exact nativeHeat066Init03_formula
    · exact nativeHeat066Init04_formula
    · exact nativeHeat066Init05_formula
    · exact nativeHeat066Init06_formula
    · exact nativeHeat066Init07_formula
    · exact nativeHeat066Init08_formula
    · exact nativeHeat066Init09_formula
    · exact nativeHeat066Init10_formula
    · exact nativeHeat066Init11_formula
    · exact nativeHeat066Init12_formula
    · exact nativeHeat066Init13_formula
    · exact nativeHeat066Init14_formula
    · exact nativeHeat066Init15_formula
    · exact nativeHeat066Init16_formula
    · exact nativeHeat066Init17_formula
    · exact nativeHeat066Init18_formula
    · exact nativeHeat066Init19_formula
    · exact nativeHeat066Init20_formula
theorem nativeHeatStep_hBase_066_Gen : nativeHeatBaseGen 66 = nativeHeat066Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_066_Gen, nativeHeatStep_hInit_066_Gen, nativeHeat066Base_formula]

theorem nativeHeatStep_hFixed_066_Gen : nativeHeatFixedGen 66 = nativeHeat066Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_066_Gen, nativeHeatStep_hFr_066_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat066Fixed01_formula
    · exact nativeHeat066Fixed02_formula
    · exact nativeHeat066Fixed03_formula
    · exact nativeHeat066Fixed04_formula
    · exact nativeHeat066Fixed05_formula
    · exact nativeHeat066Fixed06_formula
    · exact nativeHeat066Fixed07_formula
    · exact nativeHeat066Fixed08_formula
    · exact nativeHeat066Fixed09_formula
    · exact nativeHeat066Fixed10_formula
    · exact nativeHeat066Fixed11_formula
    · exact nativeHeat066Fixed12_formula
    · exact nativeHeat066Fixed13_formula
    · exact nativeHeat066Fixed14_formula
    · exact nativeHeat066Fixed15_formula
    · exact nativeHeat066Fixed16_formula
    · exact nativeHeat066Fixed17_formula
    · exact nativeHeat066Fixed18_formula
    · exact nativeHeat066Fixed19_formula
    · exact nativeHeat066Fixed20_formula

theorem nativeHeatStep_chk_066_Gen :
    nativeHeatPassRootsOk nativeGap067Old nativeHeat066Frames nativeHeat066Coef nativeHeat066Fixed nativeHeat066Base 48 nativeHeat066Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_066_Gen : NativeHeatStepPassNum 66 := by
  refine nativeHeatStepPassNum_of_literals 66 nativeGap067Old nativeHeat066Frames (nativeHeatExpArg nativeGap067Old)
    nativeHeat066Exp nativeHeat066Coef nativeHeat066Fixed nativeHeat066Init nativeHeat066Base nativeHeatStep_hOld_066_Gen
    nativeHeatStep_hFr_066_Gen nativeHeatStep_hArg_066_Gen nativeHeatStep_hExp_066_Gen
    nativeHeatStep_hCoef_066_Gen nativeHeatStep_hFixed_066_Gen
    nativeHeatStep_hInit_066_Gen nativeHeatStep_hBase_066_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_066_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_066_Gen :
    nativeHeatY0Gen 66 = nativeShiftedFrame 1 (min nativeGap067Old.x nativeGap067Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_066_Gen, nativeHeatStep_hInd_066_Gen]

theorem nativeHeatStepFrameNum_066_Gen : NativeHeatStepFrameNum 66 := by
  have h1 := nativeHeatStep_hOld_066_Gen
  have h2 := nativeHeatStep_hInd_066_Gen
  have h3 := nativeHeatStep_hVar_066_Gen
  have h4 := nativeHeatStep_hQm_066_Gen
  have h5 := nativeHeatStep_hQN_066_Gen
  have h6 := nativeHeatStep_hY0_066_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_066_Gen : NativeHeatStepIndivNum 66 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 66 (by norm_num)) = nativeGap067Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_066_Gen]; exact nativeGap067Old_source
  · rw [hc, nativeHeatStep_hInd_066_Gen]; exact nativeGap067Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_066_Gen : nativeHeatY48Gen 66 = nativeHeat066Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_066_Gen, nativeHeatStep_hFr_066_Gen,
    nativeHeatStep_hCoef_066_Gen, nativeHeatStep_hFixed_066_Gen,
    nativeHeatStep_hBase_066_Gen]
  exact nativeHeat066All48

theorem nativeHeatResultGen_066 : nativeHeatResultGen 66 = nativeHeat066Result := by
  rw [← nativeHeat066Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_066_Gen, nativeHeatStep_hY0_066_Gen, nativeHeatStep_hExp_066_Gen,
    nativeHeatStep_hInit_066_Gen, nativeHeatStep_hFixed_066_Gen]

end ASDExplicitGamma.Native

end
