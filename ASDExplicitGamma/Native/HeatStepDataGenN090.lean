module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat090Complete
public import ASDExplicitGamma.Numerics.Native.Gap091Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_090_Gen : nativeHeatOldRowGen 90 = nativeGap091Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_090_Gen : nativeHeatIndividualGen 90 = nativeGap091Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_090_Gen : nativeHeatGenVariance 90 = nativeHeat090Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_090_Gen, nativeHeat090Variance_formula]

theorem nativeHeatStep_hSpec_090_Gen : nativeHeatGenSpectral 90 = nativeHeat090Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_090_Gen, nativeHeat090Variance_formula]

theorem nativeHeatStep_hQm_090_Gen : nativeHeatGenQm 90 = nativeHeat090Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_090_Gen, nativeHeatStep_hSpec_090_Gen,
    nativeHeat090Qm_formula]

theorem nativeHeatStep_hQN_090_Gen : nativeHeatQNGen 90 = nativeHeat090QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_090_Gen, nativeHeat090QN_formula]

theorem nativeHeatStep_hFr_090_Gen : nativeHeatFramesGen 90 = nativeHeat090Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_090_Gen, nativeHeatStep_hInd_090_Gen,
    nativeHeatStep_hVar_090_Gen, nativeHeatStep_hQN_090_Gen, nativeHeat090Frames_formula]

theorem nativeHeatStep_hArg_090_Gen : nativeHeatExpArgGen 90 = nativeHeatExpArg nativeGap091Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_090_Gen]

theorem nativeHeatStep_hExp_090_Gen : nativeHeatExpGen 90 = nativeHeat090Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_090_Gen, nativeHeat090Exp_formula]

theorem nativeHeatStep_hCoef_090_Gen : nativeHeatCoefGen 90 = nativeHeat090Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_090_Gen, nativeHeat090Coef_formula]

theorem nativeHeatStep_hInit_090_Gen : nativeHeatInitGen 90 = nativeHeat090Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_090_Gen, nativeHeatStep_hVar_090_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat090Init00_formula
    · exact nativeHeat090Init01_formula
    · exact nativeHeat090Init02_formula
    · exact nativeHeat090Init03_formula
    · exact nativeHeat090Init04_formula
    · exact nativeHeat090Init05_formula
    · exact nativeHeat090Init06_formula
    · exact nativeHeat090Init07_formula
    · exact nativeHeat090Init08_formula
    · exact nativeHeat090Init09_formula
    · exact nativeHeat090Init10_formula
    · exact nativeHeat090Init11_formula
    · exact nativeHeat090Init12_formula
    · exact nativeHeat090Init13_formula
    · exact nativeHeat090Init14_formula
    · exact nativeHeat090Init15_formula
    · exact nativeHeat090Init16_formula
    · exact nativeHeat090Init17_formula
    · exact nativeHeat090Init18_formula
    · exact nativeHeat090Init19_formula
    · exact nativeHeat090Init20_formula
theorem nativeHeatStep_hBase_090_Gen : nativeHeatBaseGen 90 = nativeHeat090Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_090_Gen, nativeHeatStep_hInit_090_Gen, nativeHeat090Base_formula]

theorem nativeHeatStep_hFixed_090_Gen : nativeHeatFixedGen 90 = nativeHeat090Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_090_Gen, nativeHeatStep_hFr_090_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat090Fixed01_formula
    · exact nativeHeat090Fixed02_formula
    · exact nativeHeat090Fixed03_formula
    · exact nativeHeat090Fixed04_formula
    · exact nativeHeat090Fixed05_formula
    · exact nativeHeat090Fixed06_formula
    · exact nativeHeat090Fixed07_formula
    · exact nativeHeat090Fixed08_formula
    · exact nativeHeat090Fixed09_formula
    · exact nativeHeat090Fixed10_formula
    · exact nativeHeat090Fixed11_formula
    · exact nativeHeat090Fixed12_formula
    · exact nativeHeat090Fixed13_formula
    · exact nativeHeat090Fixed14_formula
    · exact nativeHeat090Fixed15_formula
    · exact nativeHeat090Fixed16_formula
    · exact nativeHeat090Fixed17_formula
    · exact nativeHeat090Fixed18_formula
    · exact nativeHeat090Fixed19_formula
    · exact nativeHeat090Fixed20_formula

theorem nativeHeatStep_chk_090_Gen :
    nativeHeatPassRootsOk nativeGap091Old nativeHeat090Frames nativeHeat090Coef nativeHeat090Fixed nativeHeat090Base 48 nativeHeat090Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_090_Gen : NativeHeatStepPassNum 90 := by
  refine nativeHeatStepPassNum_of_literals 90 nativeGap091Old nativeHeat090Frames (nativeHeatExpArg nativeGap091Old)
    nativeHeat090Exp nativeHeat090Coef nativeHeat090Fixed nativeHeat090Init nativeHeat090Base nativeHeatStep_hOld_090_Gen
    nativeHeatStep_hFr_090_Gen nativeHeatStep_hArg_090_Gen nativeHeatStep_hExp_090_Gen
    nativeHeatStep_hCoef_090_Gen nativeHeatStep_hFixed_090_Gen
    nativeHeatStep_hInit_090_Gen nativeHeatStep_hBase_090_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_090_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_090_Gen :
    nativeHeatY0Gen 90 = nativeShiftedFrame 1 (min nativeGap091Old.x nativeGap091Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_090_Gen, nativeHeatStep_hInd_090_Gen]

theorem nativeHeatStepFrameNum_090_Gen : NativeHeatStepFrameNum 90 := by
  have h1 := nativeHeatStep_hOld_090_Gen
  have h2 := nativeHeatStep_hInd_090_Gen
  have h3 := nativeHeatStep_hVar_090_Gen
  have h4 := nativeHeatStep_hQm_090_Gen
  have h5 := nativeHeatStep_hQN_090_Gen
  have h6 := nativeHeatStep_hY0_090_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_090_Gen : NativeHeatStepIndivNum 90 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 90 (by norm_num)) = nativeGap091Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_090_Gen]; exact nativeGap091Old_source
  · rw [hc, nativeHeatStep_hInd_090_Gen]; exact nativeGap091Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_090_Gen : nativeHeatY48Gen 90 = nativeHeat090Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_090_Gen, nativeHeatStep_hFr_090_Gen,
    nativeHeatStep_hCoef_090_Gen, nativeHeatStep_hFixed_090_Gen,
    nativeHeatStep_hBase_090_Gen]
  exact nativeHeat090All48

theorem nativeHeatResultGen_090 : nativeHeatResultGen 90 = nativeHeat090Result := by
  rw [← nativeHeat090Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_090_Gen, nativeHeatStep_hY0_090_Gen, nativeHeatStep_hExp_090_Gen,
    nativeHeatStep_hInit_090_Gen, nativeHeatStep_hFixed_090_Gen]

end ASDExplicitGamma.Native

end
