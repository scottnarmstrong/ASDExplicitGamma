module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat035Complete
public import ASDExplicitGamma.Numerics.Native.Gap036Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_035_Gen : nativeHeatOldRowGen 35 = nativeGap036Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_035_Gen : nativeHeatIndividualGen 35 = nativeGap036Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_035_Gen : nativeHeatGenVariance 35 = nativeHeat035Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_035_Gen, nativeHeat035Variance_formula]

theorem nativeHeatStep_hSpec_035_Gen : nativeHeatGenSpectral 35 = nativeHeat035Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_035_Gen, nativeHeat035Variance_formula]

theorem nativeHeatStep_hQm_035_Gen : nativeHeatGenQm 35 = nativeHeat035Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_035_Gen, nativeHeatStep_hSpec_035_Gen,
    nativeHeat035Qm_formula]

theorem nativeHeatStep_hQN_035_Gen : nativeHeatQNGen 35 = nativeHeat035QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_035_Gen, nativeHeat035QN_formula]

theorem nativeHeatStep_hFr_035_Gen : nativeHeatFramesGen 35 = nativeHeat035Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_035_Gen, nativeHeatStep_hInd_035_Gen,
    nativeHeatStep_hVar_035_Gen, nativeHeatStep_hQN_035_Gen, nativeHeat035Frames_formula]

theorem nativeHeatStep_hArg_035_Gen : nativeHeatExpArgGen 35 = nativeHeatExpArg nativeGap036Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_035_Gen]

theorem nativeHeatStep_hExp_035_Gen : nativeHeatExpGen 35 = nativeHeat035Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_035_Gen, nativeHeat035Exp_formula]

theorem nativeHeatStep_hCoef_035_Gen : nativeHeatCoefGen 35 = nativeHeat035Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_035_Gen, nativeHeat035Coef_formula]

theorem nativeHeatStep_hInit_035_Gen : nativeHeatInitGen 35 = nativeHeat035Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_035_Gen, nativeHeatStep_hVar_035_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat035Init00_formula
    · exact nativeHeat035Init01_formula
    · exact nativeHeat035Init02_formula
    · exact nativeHeat035Init03_formula
    · exact nativeHeat035Init04_formula
    · exact nativeHeat035Init05_formula
    · exact nativeHeat035Init06_formula
    · exact nativeHeat035Init07_formula
    · exact nativeHeat035Init08_formula
    · exact nativeHeat035Init09_formula
    · exact nativeHeat035Init10_formula
    · exact nativeHeat035Init11_formula
    · exact nativeHeat035Init12_formula
    · exact nativeHeat035Init13_formula
    · exact nativeHeat035Init14_formula
    · exact nativeHeat035Init15_formula
    · exact nativeHeat035Init16_formula
    · exact nativeHeat035Init17_formula
    · exact nativeHeat035Init18_formula
    · exact nativeHeat035Init19_formula
    · exact nativeHeat035Init20_formula
theorem nativeHeatStep_hBase_035_Gen : nativeHeatBaseGen 35 = nativeHeat035Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_035_Gen, nativeHeatStep_hInit_035_Gen, nativeHeat035Base_formula]

theorem nativeHeatStep_hFixed_035_Gen : nativeHeatFixedGen 35 = nativeHeat035Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_035_Gen, nativeHeatStep_hFr_035_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat035Fixed01_formula
    · exact nativeHeat035Fixed02_formula
    · exact nativeHeat035Fixed03_formula
    · exact nativeHeat035Fixed04_formula
    · exact nativeHeat035Fixed05_formula
    · exact nativeHeat035Fixed06_formula
    · exact nativeHeat035Fixed07_formula
    · exact nativeHeat035Fixed08_formula
    · exact nativeHeat035Fixed09_formula
    · exact nativeHeat035Fixed10_formula
    · exact nativeHeat035Fixed11_formula
    · exact nativeHeat035Fixed12_formula
    · exact nativeHeat035Fixed13_formula
    · exact nativeHeat035Fixed14_formula
    · exact nativeHeat035Fixed15_formula
    · exact nativeHeat035Fixed16_formula
    · exact nativeHeat035Fixed17_formula
    · exact nativeHeat035Fixed18_formula
    · exact nativeHeat035Fixed19_formula
    · exact nativeHeat035Fixed20_formula

theorem nativeHeatStep_chk_035_Gen :
    nativeHeatPassRootsOk nativeGap036Old nativeHeat035Frames nativeHeat035Coef nativeHeat035Fixed nativeHeat035Base 48 nativeHeat035Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_035_Gen : NativeHeatStepPassNum 35 := by
  refine nativeHeatStepPassNum_of_literals 35 nativeGap036Old nativeHeat035Frames (nativeHeatExpArg nativeGap036Old)
    nativeHeat035Exp nativeHeat035Coef nativeHeat035Fixed nativeHeat035Init nativeHeat035Base nativeHeatStep_hOld_035_Gen
    nativeHeatStep_hFr_035_Gen nativeHeatStep_hArg_035_Gen nativeHeatStep_hExp_035_Gen
    nativeHeatStep_hCoef_035_Gen nativeHeatStep_hFixed_035_Gen
    nativeHeatStep_hInit_035_Gen nativeHeatStep_hBase_035_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_035_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_035_Gen :
    nativeHeatY0Gen 35 = nativeShiftedFrame 1 (min nativeGap036Old.x nativeGap036Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_035_Gen, nativeHeatStep_hInd_035_Gen]

theorem nativeHeatStepFrameNum_035_Gen : NativeHeatStepFrameNum 35 := by
  have h1 := nativeHeatStep_hOld_035_Gen
  have h2 := nativeHeatStep_hInd_035_Gen
  have h3 := nativeHeatStep_hVar_035_Gen
  have h4 := nativeHeatStep_hQm_035_Gen
  have h5 := nativeHeatStep_hQN_035_Gen
  have h6 := nativeHeatStep_hY0_035_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_035_Gen : NativeHeatStepIndivNum 35 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 35 (by norm_num)) = nativeGap036Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_035_Gen]; exact nativeGap036Old_source
  · rw [hc, nativeHeatStep_hInd_035_Gen]; exact nativeGap036Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_035_Gen : nativeHeatY48Gen 35 = nativeHeat035Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_035_Gen, nativeHeatStep_hFr_035_Gen,
    nativeHeatStep_hCoef_035_Gen, nativeHeatStep_hFixed_035_Gen,
    nativeHeatStep_hBase_035_Gen]
  exact nativeHeat035All48

theorem nativeHeatResultGen_035 : nativeHeatResultGen 35 = nativeHeat035Result := by
  rw [← nativeHeat035Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_035_Gen, nativeHeatStep_hY0_035_Gen, nativeHeatStep_hExp_035_Gen,
    nativeHeatStep_hInit_035_Gen, nativeHeatStep_hFixed_035_Gen]

end ASDExplicitGamma.Native

end
