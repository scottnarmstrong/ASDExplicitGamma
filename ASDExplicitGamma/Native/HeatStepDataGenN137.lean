module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat137Complete
public import ASDExplicitGamma.Numerics.Native.Gap138Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_137_Gen : nativeHeatOldRowGen 137 = nativeGap138Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_137_Gen : nativeHeatIndividualGen 137 = nativeGap138Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_137_Gen : nativeHeatGenVariance 137 = nativeHeat137Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_137_Gen, nativeHeat137Variance_formula]

theorem nativeHeatStep_hSpec_137_Gen : nativeHeatGenSpectral 137 = nativeHeat137Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_137_Gen, nativeHeat137Variance_formula]

theorem nativeHeatStep_hQm_137_Gen : nativeHeatGenQm 137 = nativeHeat137Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_137_Gen, nativeHeatStep_hSpec_137_Gen,
    nativeHeat137Qm_formula]

theorem nativeHeatStep_hQN_137_Gen : nativeHeatQNGen 137 = nativeHeat137QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_137_Gen, nativeHeat137QN_formula]

theorem nativeHeatStep_hFr_137_Gen : nativeHeatFramesGen 137 = nativeHeat137Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_137_Gen, nativeHeatStep_hInd_137_Gen,
    nativeHeatStep_hVar_137_Gen, nativeHeatStep_hQN_137_Gen, nativeHeat137Frames_formula]

theorem nativeHeatStep_hArg_137_Gen : nativeHeatExpArgGen 137 = nativeHeatExpArg nativeGap138Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_137_Gen]

theorem nativeHeatStep_hExp_137_Gen : nativeHeatExpGen 137 = nativeHeat137Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_137_Gen, nativeHeat137Exp_formula]

theorem nativeHeatStep_hCoef_137_Gen : nativeHeatCoefGen 137 = nativeHeat137Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_137_Gen, nativeHeat137Coef_formula]

theorem nativeHeatStep_hInit_137_Gen : nativeHeatInitGen 137 = nativeHeat137Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_137_Gen, nativeHeatStep_hVar_137_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat137Init00_formula
    · exact nativeHeat137Init01_formula
    · exact nativeHeat137Init02_formula
    · exact nativeHeat137Init03_formula
    · exact nativeHeat137Init04_formula
    · exact nativeHeat137Init05_formula
    · exact nativeHeat137Init06_formula
    · exact nativeHeat137Init07_formula
    · exact nativeHeat137Init08_formula
    · exact nativeHeat137Init09_formula
    · exact nativeHeat137Init10_formula
    · exact nativeHeat137Init11_formula
    · exact nativeHeat137Init12_formula
    · exact nativeHeat137Init13_formula
    · exact nativeHeat137Init14_formula
    · exact nativeHeat137Init15_formula
    · exact nativeHeat137Init16_formula
    · exact nativeHeat137Init17_formula
    · exact nativeHeat137Init18_formula
    · exact nativeHeat137Init19_formula
    · exact nativeHeat137Init20_formula
theorem nativeHeatStep_hBase_137_Gen : nativeHeatBaseGen 137 = nativeHeat137Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_137_Gen, nativeHeatStep_hInit_137_Gen, nativeHeat137Base_formula]

theorem nativeHeatStep_hFixed_137_Gen : nativeHeatFixedGen 137 = nativeHeat137Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_137_Gen, nativeHeatStep_hFr_137_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat137Fixed01_formula
    · exact nativeHeat137Fixed02_formula
    · exact nativeHeat137Fixed03_formula
    · exact nativeHeat137Fixed04_formula
    · exact nativeHeat137Fixed05_formula
    · exact nativeHeat137Fixed06_formula
    · exact nativeHeat137Fixed07_formula
    · exact nativeHeat137Fixed08_formula
    · exact nativeHeat137Fixed09_formula
    · exact nativeHeat137Fixed10_formula
    · exact nativeHeat137Fixed11_formula
    · exact nativeHeat137Fixed12_formula
    · exact nativeHeat137Fixed13_formula
    · exact nativeHeat137Fixed14_formula
    · exact nativeHeat137Fixed15_formula
    · exact nativeHeat137Fixed16_formula
    · exact nativeHeat137Fixed17_formula
    · exact nativeHeat137Fixed18_formula
    · exact nativeHeat137Fixed19_formula
    · exact nativeHeat137Fixed20_formula

theorem nativeHeatStep_chk_137_Gen :
    nativeHeatPassRootsOk nativeGap138Old nativeHeat137Frames nativeHeat137Coef nativeHeat137Fixed nativeHeat137Base 48 nativeHeat137Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_137_Gen : NativeHeatStepPassNum 137 := by
  refine nativeHeatStepPassNum_of_literals 137 nativeGap138Old nativeHeat137Frames (nativeHeatExpArg nativeGap138Old)
    nativeHeat137Exp nativeHeat137Coef nativeHeat137Fixed nativeHeat137Init nativeHeat137Base nativeHeatStep_hOld_137_Gen
    nativeHeatStep_hFr_137_Gen nativeHeatStep_hArg_137_Gen nativeHeatStep_hExp_137_Gen
    nativeHeatStep_hCoef_137_Gen nativeHeatStep_hFixed_137_Gen
    nativeHeatStep_hInit_137_Gen nativeHeatStep_hBase_137_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_137_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_137_Gen :
    nativeHeatY0Gen 137 = nativeShiftedFrame 1 (min nativeGap138Old.x nativeGap138Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_137_Gen, nativeHeatStep_hInd_137_Gen]

theorem nativeHeatStepFrameNum_137_Gen : NativeHeatStepFrameNum 137 := by
  have h1 := nativeHeatStep_hOld_137_Gen
  have h2 := nativeHeatStep_hInd_137_Gen
  have h3 := nativeHeatStep_hVar_137_Gen
  have h4 := nativeHeatStep_hQm_137_Gen
  have h5 := nativeHeatStep_hQN_137_Gen
  have h6 := nativeHeatStep_hY0_137_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_137_Gen : NativeHeatStepIndivNum 137 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 137 (by norm_num)) = nativeGap138Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_137_Gen]; exact nativeGap138Old_source
  · rw [hc, nativeHeatStep_hInd_137_Gen]; exact nativeGap138Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_137_Gen : nativeHeatY48Gen 137 = nativeHeat137Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_137_Gen, nativeHeatStep_hFr_137_Gen,
    nativeHeatStep_hCoef_137_Gen, nativeHeatStep_hFixed_137_Gen,
    nativeHeatStep_hBase_137_Gen]
  exact nativeHeat137All48

theorem nativeHeatResultGen_137 : nativeHeatResultGen 137 = nativeHeat137Result := by
  rw [← nativeHeat137Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_137_Gen, nativeHeatStep_hY0_137_Gen, nativeHeatStep_hExp_137_Gen,
    nativeHeatStep_hInit_137_Gen, nativeHeatStep_hFixed_137_Gen]

end ASDExplicitGamma.Native

end
