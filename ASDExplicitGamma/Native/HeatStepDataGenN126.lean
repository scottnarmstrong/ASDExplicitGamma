module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat126Complete
public import ASDExplicitGamma.Numerics.Native.Gap127Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_126_Gen : nativeHeatOldRowGen 126 = nativeGap127Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_126_Gen : nativeHeatIndividualGen 126 = nativeGap127Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_126_Gen : nativeHeatGenVariance 126 = nativeHeat126Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_126_Gen, nativeHeat126Variance_formula]

theorem nativeHeatStep_hSpec_126_Gen : nativeHeatGenSpectral 126 = nativeHeat126Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_126_Gen, nativeHeat126Variance_formula]

theorem nativeHeatStep_hQm_126_Gen : nativeHeatGenQm 126 = nativeHeat126Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_126_Gen, nativeHeatStep_hSpec_126_Gen,
    nativeHeat126Qm_formula]

theorem nativeHeatStep_hQN_126_Gen : nativeHeatQNGen 126 = nativeHeat126QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_126_Gen, nativeHeat126QN_formula]

theorem nativeHeatStep_hFr_126_Gen : nativeHeatFramesGen 126 = nativeHeat126Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_126_Gen, nativeHeatStep_hInd_126_Gen,
    nativeHeatStep_hVar_126_Gen, nativeHeatStep_hQN_126_Gen, nativeHeat126Frames_formula]

theorem nativeHeatStep_hArg_126_Gen : nativeHeatExpArgGen 126 = nativeHeatExpArg nativeGap127Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_126_Gen]

theorem nativeHeatStep_hExp_126_Gen : nativeHeatExpGen 126 = nativeHeat126Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_126_Gen, nativeHeat126Exp_formula]

theorem nativeHeatStep_hCoef_126_Gen : nativeHeatCoefGen 126 = nativeHeat126Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_126_Gen, nativeHeat126Coef_formula]

theorem nativeHeatStep_hInit_126_Gen : nativeHeatInitGen 126 = nativeHeat126Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_126_Gen, nativeHeatStep_hVar_126_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat126Init00_formula
    · exact nativeHeat126Init01_formula
    · exact nativeHeat126Init02_formula
    · exact nativeHeat126Init03_formula
    · exact nativeHeat126Init04_formula
    · exact nativeHeat126Init05_formula
    · exact nativeHeat126Init06_formula
    · exact nativeHeat126Init07_formula
    · exact nativeHeat126Init08_formula
    · exact nativeHeat126Init09_formula
    · exact nativeHeat126Init10_formula
    · exact nativeHeat126Init11_formula
    · exact nativeHeat126Init12_formula
    · exact nativeHeat126Init13_formula
    · exact nativeHeat126Init14_formula
    · exact nativeHeat126Init15_formula
    · exact nativeHeat126Init16_formula
    · exact nativeHeat126Init17_formula
    · exact nativeHeat126Init18_formula
    · exact nativeHeat126Init19_formula
    · exact nativeHeat126Init20_formula
theorem nativeHeatStep_hBase_126_Gen : nativeHeatBaseGen 126 = nativeHeat126Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_126_Gen, nativeHeatStep_hInit_126_Gen, nativeHeat126Base_formula]

theorem nativeHeatStep_hFixed_126_Gen : nativeHeatFixedGen 126 = nativeHeat126Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_126_Gen, nativeHeatStep_hFr_126_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat126Fixed01_formula
    · exact nativeHeat126Fixed02_formula
    · exact nativeHeat126Fixed03_formula
    · exact nativeHeat126Fixed04_formula
    · exact nativeHeat126Fixed05_formula
    · exact nativeHeat126Fixed06_formula
    · exact nativeHeat126Fixed07_formula
    · exact nativeHeat126Fixed08_formula
    · exact nativeHeat126Fixed09_formula
    · exact nativeHeat126Fixed10_formula
    · exact nativeHeat126Fixed11_formula
    · exact nativeHeat126Fixed12_formula
    · exact nativeHeat126Fixed13_formula
    · exact nativeHeat126Fixed14_formula
    · exact nativeHeat126Fixed15_formula
    · exact nativeHeat126Fixed16_formula
    · exact nativeHeat126Fixed17_formula
    · exact nativeHeat126Fixed18_formula
    · exact nativeHeat126Fixed19_formula
    · exact nativeHeat126Fixed20_formula

theorem nativeHeatStep_chk_126_Gen :
    nativeHeatPassRootsOk nativeGap127Old nativeHeat126Frames nativeHeat126Coef nativeHeat126Fixed nativeHeat126Base 48 nativeHeat126Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_126_Gen : NativeHeatStepPassNum 126 := by
  refine nativeHeatStepPassNum_of_literals 126 nativeGap127Old nativeHeat126Frames (nativeHeatExpArg nativeGap127Old)
    nativeHeat126Exp nativeHeat126Coef nativeHeat126Fixed nativeHeat126Init nativeHeat126Base nativeHeatStep_hOld_126_Gen
    nativeHeatStep_hFr_126_Gen nativeHeatStep_hArg_126_Gen nativeHeatStep_hExp_126_Gen
    nativeHeatStep_hCoef_126_Gen nativeHeatStep_hFixed_126_Gen
    nativeHeatStep_hInit_126_Gen nativeHeatStep_hBase_126_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_126_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_126_Gen :
    nativeHeatY0Gen 126 = nativeShiftedFrame 1 (min nativeGap127Old.x nativeGap127Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_126_Gen, nativeHeatStep_hInd_126_Gen]

theorem nativeHeatStepFrameNum_126_Gen : NativeHeatStepFrameNum 126 := by
  have h1 := nativeHeatStep_hOld_126_Gen
  have h2 := nativeHeatStep_hInd_126_Gen
  have h3 := nativeHeatStep_hVar_126_Gen
  have h4 := nativeHeatStep_hQm_126_Gen
  have h5 := nativeHeatStep_hQN_126_Gen
  have h6 := nativeHeatStep_hY0_126_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_126_Gen : NativeHeatStepIndivNum 126 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 126 (by norm_num)) = nativeGap127Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_126_Gen]; exact nativeGap127Old_source
  · rw [hc, nativeHeatStep_hInd_126_Gen]; exact nativeGap127Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_126_Gen : nativeHeatY48Gen 126 = nativeHeat126Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_126_Gen, nativeHeatStep_hFr_126_Gen,
    nativeHeatStep_hCoef_126_Gen, nativeHeatStep_hFixed_126_Gen,
    nativeHeatStep_hBase_126_Gen]
  exact nativeHeat126All48

theorem nativeHeatResultGen_126 : nativeHeatResultGen 126 = nativeHeat126Result := by
  rw [← nativeHeat126Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_126_Gen, nativeHeatStep_hY0_126_Gen, nativeHeatStep_hExp_126_Gen,
    nativeHeatStep_hInit_126_Gen, nativeHeatStep_hFixed_126_Gen]

end ASDExplicitGamma.Native

end
