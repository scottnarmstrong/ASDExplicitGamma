module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat046Complete
public import ASDExplicitGamma.Numerics.Native.Gap047Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_046_Gen : nativeHeatOldRowGen 46 = nativeGap047Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_046_Gen : nativeHeatIndividualGen 46 = nativeGap047Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_046_Gen : nativeHeatGenVariance 46 = nativeHeat046Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_046_Gen, nativeHeat046Variance_formula]

theorem nativeHeatStep_hSpec_046_Gen : nativeHeatGenSpectral 46 = nativeHeat046Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_046_Gen, nativeHeat046Variance_formula]

theorem nativeHeatStep_hQm_046_Gen : nativeHeatGenQm 46 = nativeHeat046Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_046_Gen, nativeHeatStep_hSpec_046_Gen,
    nativeHeat046Qm_formula]

theorem nativeHeatStep_hQN_046_Gen : nativeHeatQNGen 46 = nativeHeat046QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_046_Gen, nativeHeat046QN_formula]

theorem nativeHeatStep_hFr_046_Gen : nativeHeatFramesGen 46 = nativeHeat046Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_046_Gen, nativeHeatStep_hInd_046_Gen,
    nativeHeatStep_hVar_046_Gen, nativeHeatStep_hQN_046_Gen, nativeHeat046Frames_formula]

theorem nativeHeatStep_hArg_046_Gen : nativeHeatExpArgGen 46 = nativeHeatExpArg nativeGap047Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_046_Gen]

theorem nativeHeatStep_hExp_046_Gen : nativeHeatExpGen 46 = nativeHeat046Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_046_Gen, nativeHeat046Exp_formula]

theorem nativeHeatStep_hCoef_046_Gen : nativeHeatCoefGen 46 = nativeHeat046Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_046_Gen, nativeHeat046Coef_formula]

theorem nativeHeatStep_hInit_046_Gen : nativeHeatInitGen 46 = nativeHeat046Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_046_Gen, nativeHeatStep_hVar_046_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat046Init00_formula
    · exact nativeHeat046Init01_formula
    · exact nativeHeat046Init02_formula
    · exact nativeHeat046Init03_formula
    · exact nativeHeat046Init04_formula
    · exact nativeHeat046Init05_formula
    · exact nativeHeat046Init06_formula
    · exact nativeHeat046Init07_formula
    · exact nativeHeat046Init08_formula
    · exact nativeHeat046Init09_formula
    · exact nativeHeat046Init10_formula
    · exact nativeHeat046Init11_formula
    · exact nativeHeat046Init12_formula
    · exact nativeHeat046Init13_formula
    · exact nativeHeat046Init14_formula
    · exact nativeHeat046Init15_formula
    · exact nativeHeat046Init16_formula
    · exact nativeHeat046Init17_formula
    · exact nativeHeat046Init18_formula
    · exact nativeHeat046Init19_formula
    · exact nativeHeat046Init20_formula
theorem nativeHeatStep_hBase_046_Gen : nativeHeatBaseGen 46 = nativeHeat046Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_046_Gen, nativeHeatStep_hInit_046_Gen, nativeHeat046Base_formula]

theorem nativeHeatStep_hFixed_046_Gen : nativeHeatFixedGen 46 = nativeHeat046Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_046_Gen, nativeHeatStep_hFr_046_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat046Fixed01_formula
    · exact nativeHeat046Fixed02_formula
    · exact nativeHeat046Fixed03_formula
    · exact nativeHeat046Fixed04_formula
    · exact nativeHeat046Fixed05_formula
    · exact nativeHeat046Fixed06_formula
    · exact nativeHeat046Fixed07_formula
    · exact nativeHeat046Fixed08_formula
    · exact nativeHeat046Fixed09_formula
    · exact nativeHeat046Fixed10_formula
    · exact nativeHeat046Fixed11_formula
    · exact nativeHeat046Fixed12_formula
    · exact nativeHeat046Fixed13_formula
    · exact nativeHeat046Fixed14_formula
    · exact nativeHeat046Fixed15_formula
    · exact nativeHeat046Fixed16_formula
    · exact nativeHeat046Fixed17_formula
    · exact nativeHeat046Fixed18_formula
    · exact nativeHeat046Fixed19_formula
    · exact nativeHeat046Fixed20_formula

theorem nativeHeatStep_chk_046_Gen :
    nativeHeatPassRootsOk nativeGap047Old nativeHeat046Frames nativeHeat046Coef nativeHeat046Fixed nativeHeat046Base 48 nativeHeat046Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_046_Gen : NativeHeatStepPassNum 46 := by
  refine nativeHeatStepPassNum_of_literals 46 nativeGap047Old nativeHeat046Frames (nativeHeatExpArg nativeGap047Old)
    nativeHeat046Exp nativeHeat046Coef nativeHeat046Fixed nativeHeat046Init nativeHeat046Base nativeHeatStep_hOld_046_Gen
    nativeHeatStep_hFr_046_Gen nativeHeatStep_hArg_046_Gen nativeHeatStep_hExp_046_Gen
    nativeHeatStep_hCoef_046_Gen nativeHeatStep_hFixed_046_Gen
    nativeHeatStep_hInit_046_Gen nativeHeatStep_hBase_046_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_046_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_046_Gen :
    nativeHeatY0Gen 46 = nativeShiftedFrame 1 (min nativeGap047Old.x nativeGap047Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_046_Gen, nativeHeatStep_hInd_046_Gen]

theorem nativeHeatStepFrameNum_046_Gen : NativeHeatStepFrameNum 46 := by
  have h1 := nativeHeatStep_hOld_046_Gen
  have h2 := nativeHeatStep_hInd_046_Gen
  have h3 := nativeHeatStep_hVar_046_Gen
  have h4 := nativeHeatStep_hQm_046_Gen
  have h5 := nativeHeatStep_hQN_046_Gen
  have h6 := nativeHeatStep_hY0_046_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_046_Gen : NativeHeatStepIndivNum 46 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 46 (by norm_num)) = nativeGap047Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_046_Gen]; exact nativeGap047Old_source
  · rw [hc, nativeHeatStep_hInd_046_Gen]; exact nativeGap047Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_046_Gen : nativeHeatY48Gen 46 = nativeHeat046Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_046_Gen, nativeHeatStep_hFr_046_Gen,
    nativeHeatStep_hCoef_046_Gen, nativeHeatStep_hFixed_046_Gen,
    nativeHeatStep_hBase_046_Gen]
  exact nativeHeat046All48

theorem nativeHeatResultGen_046 : nativeHeatResultGen 46 = nativeHeat046Result := by
  rw [← nativeHeat046Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_046_Gen, nativeHeatStep_hY0_046_Gen, nativeHeatStep_hExp_046_Gen,
    nativeHeatStep_hInit_046_Gen, nativeHeatStep_hFixed_046_Gen]

end ASDExplicitGamma.Native

end
