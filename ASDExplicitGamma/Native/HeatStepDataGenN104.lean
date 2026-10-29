module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat104Complete
public import ASDExplicitGamma.Numerics.Native.Gap105Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_104_Gen : nativeHeatOldRowGen 104 = nativeGap105Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_104_Gen : nativeHeatIndividualGen 104 = nativeGap105Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_104_Gen : nativeHeatGenVariance 104 = nativeHeat104Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_104_Gen, nativeHeat104Variance_formula]

theorem nativeHeatStep_hSpec_104_Gen : nativeHeatGenSpectral 104 = nativeHeat104Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_104_Gen, nativeHeat104Variance_formula]

theorem nativeHeatStep_hQm_104_Gen : nativeHeatGenQm 104 = nativeHeat104Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_104_Gen, nativeHeatStep_hSpec_104_Gen,
    nativeHeat104Qm_formula]

theorem nativeHeatStep_hQN_104_Gen : nativeHeatQNGen 104 = nativeHeat104QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_104_Gen, nativeHeat104QN_formula]

theorem nativeHeatStep_hFr_104_Gen : nativeHeatFramesGen 104 = nativeHeat104Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_104_Gen, nativeHeatStep_hInd_104_Gen,
    nativeHeatStep_hVar_104_Gen, nativeHeatStep_hQN_104_Gen, nativeHeat104Frames_formula]

theorem nativeHeatStep_hArg_104_Gen : nativeHeatExpArgGen 104 = nativeHeatExpArg nativeGap105Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_104_Gen]

theorem nativeHeatStep_hExp_104_Gen : nativeHeatExpGen 104 = nativeHeat104Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_104_Gen, nativeHeat104Exp_formula]

theorem nativeHeatStep_hCoef_104_Gen : nativeHeatCoefGen 104 = nativeHeat104Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_104_Gen, nativeHeat104Coef_formula]

theorem nativeHeatStep_hInit_104_Gen : nativeHeatInitGen 104 = nativeHeat104Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_104_Gen, nativeHeatStep_hVar_104_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat104Init00_formula
    · exact nativeHeat104Init01_formula
    · exact nativeHeat104Init02_formula
    · exact nativeHeat104Init03_formula
    · exact nativeHeat104Init04_formula
    · exact nativeHeat104Init05_formula
    · exact nativeHeat104Init06_formula
    · exact nativeHeat104Init07_formula
    · exact nativeHeat104Init08_formula
    · exact nativeHeat104Init09_formula
    · exact nativeHeat104Init10_formula
    · exact nativeHeat104Init11_formula
    · exact nativeHeat104Init12_formula
    · exact nativeHeat104Init13_formula
    · exact nativeHeat104Init14_formula
    · exact nativeHeat104Init15_formula
    · exact nativeHeat104Init16_formula
    · exact nativeHeat104Init17_formula
    · exact nativeHeat104Init18_formula
    · exact nativeHeat104Init19_formula
    · exact nativeHeat104Init20_formula
theorem nativeHeatStep_hBase_104_Gen : nativeHeatBaseGen 104 = nativeHeat104Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_104_Gen, nativeHeatStep_hInit_104_Gen, nativeHeat104Base_formula]

theorem nativeHeatStep_hFixed_104_Gen : nativeHeatFixedGen 104 = nativeHeat104Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_104_Gen, nativeHeatStep_hFr_104_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat104Fixed01_formula
    · exact nativeHeat104Fixed02_formula
    · exact nativeHeat104Fixed03_formula
    · exact nativeHeat104Fixed04_formula
    · exact nativeHeat104Fixed05_formula
    · exact nativeHeat104Fixed06_formula
    · exact nativeHeat104Fixed07_formula
    · exact nativeHeat104Fixed08_formula
    · exact nativeHeat104Fixed09_formula
    · exact nativeHeat104Fixed10_formula
    · exact nativeHeat104Fixed11_formula
    · exact nativeHeat104Fixed12_formula
    · exact nativeHeat104Fixed13_formula
    · exact nativeHeat104Fixed14_formula
    · exact nativeHeat104Fixed15_formula
    · exact nativeHeat104Fixed16_formula
    · exact nativeHeat104Fixed17_formula
    · exact nativeHeat104Fixed18_formula
    · exact nativeHeat104Fixed19_formula
    · exact nativeHeat104Fixed20_formula

theorem nativeHeatStep_chk_104_Gen :
    nativeHeatPassRootsOk nativeGap105Old nativeHeat104Frames nativeHeat104Coef nativeHeat104Fixed nativeHeat104Base 48 nativeHeat104Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_104_Gen : NativeHeatStepPassNum 104 := by
  refine nativeHeatStepPassNum_of_literals 104 nativeGap105Old nativeHeat104Frames (nativeHeatExpArg nativeGap105Old)
    nativeHeat104Exp nativeHeat104Coef nativeHeat104Fixed nativeHeat104Init nativeHeat104Base nativeHeatStep_hOld_104_Gen
    nativeHeatStep_hFr_104_Gen nativeHeatStep_hArg_104_Gen nativeHeatStep_hExp_104_Gen
    nativeHeatStep_hCoef_104_Gen nativeHeatStep_hFixed_104_Gen
    nativeHeatStep_hInit_104_Gen nativeHeatStep_hBase_104_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_104_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_104_Gen :
    nativeHeatY0Gen 104 = nativeShiftedFrame 1 (min nativeGap105Old.x nativeGap105Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_104_Gen, nativeHeatStep_hInd_104_Gen]

theorem nativeHeatStepFrameNum_104_Gen : NativeHeatStepFrameNum 104 := by
  have h1 := nativeHeatStep_hOld_104_Gen
  have h2 := nativeHeatStep_hInd_104_Gen
  have h3 := nativeHeatStep_hVar_104_Gen
  have h4 := nativeHeatStep_hQm_104_Gen
  have h5 := nativeHeatStep_hQN_104_Gen
  have h6 := nativeHeatStep_hY0_104_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_104_Gen : NativeHeatStepIndivNum 104 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 104 (by norm_num)) = nativeGap105Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_104_Gen]; exact nativeGap105Old_source
  · rw [hc, nativeHeatStep_hInd_104_Gen]; exact nativeGap105Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_104_Gen : nativeHeatY48Gen 104 = nativeHeat104Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_104_Gen, nativeHeatStep_hFr_104_Gen,
    nativeHeatStep_hCoef_104_Gen, nativeHeatStep_hFixed_104_Gen,
    nativeHeatStep_hBase_104_Gen]
  exact nativeHeat104All48

theorem nativeHeatResultGen_104 : nativeHeatResultGen 104 = nativeHeat104Result := by
  rw [← nativeHeat104Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_104_Gen, nativeHeatStep_hY0_104_Gen, nativeHeatStep_hExp_104_Gen,
    nativeHeatStep_hInit_104_Gen, nativeHeatStep_hFixed_104_Gen]

end ASDExplicitGamma.Native

end
