module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat151Complete
public import ASDExplicitGamma.Numerics.Native.Gap152Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_151_Gen : nativeHeatOldRowGen 151 = nativeGap152Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_151_Gen : nativeHeatIndividualGen 151 = nativeGap152Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_151_Gen : nativeHeatGenVariance 151 = nativeHeat151Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_151_Gen, nativeHeat151Variance_formula]

theorem nativeHeatStep_hSpec_151_Gen : nativeHeatGenSpectral 151 = nativeHeat151Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_151_Gen, nativeHeat151Variance_formula]

theorem nativeHeatStep_hQm_151_Gen : nativeHeatGenQm 151 = nativeHeat151Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_151_Gen, nativeHeatStep_hSpec_151_Gen,
    nativeHeat151Qm_formula]

theorem nativeHeatStep_hQN_151_Gen : nativeHeatQNGen 151 = nativeHeat151QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_151_Gen, nativeHeat151QN_formula]

theorem nativeHeatStep_hFr_151_Gen : nativeHeatFramesGen 151 = nativeHeat151Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_151_Gen, nativeHeatStep_hInd_151_Gen,
    nativeHeatStep_hVar_151_Gen, nativeHeatStep_hQN_151_Gen, nativeHeat151Frames_formula]

theorem nativeHeatStep_hArg_151_Gen : nativeHeatExpArgGen 151 = nativeHeatExpArg nativeGap152Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_151_Gen]

theorem nativeHeatStep_hExp_151_Gen : nativeHeatExpGen 151 = nativeHeat151Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_151_Gen, nativeHeat151Exp_formula]

theorem nativeHeatStep_hCoef_151_Gen : nativeHeatCoefGen 151 = nativeHeat151Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_151_Gen, nativeHeat151Coef_formula]

theorem nativeHeatStep_hInit_151_Gen : nativeHeatInitGen 151 = nativeHeat151Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_151_Gen, nativeHeatStep_hVar_151_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat151Init00_formula
    · exact nativeHeat151Init01_formula
    · exact nativeHeat151Init02_formula
    · exact nativeHeat151Init03_formula
    · exact nativeHeat151Init04_formula
    · exact nativeHeat151Init05_formula
    · exact nativeHeat151Init06_formula
    · exact nativeHeat151Init07_formula
    · exact nativeHeat151Init08_formula
    · exact nativeHeat151Init09_formula
    · exact nativeHeat151Init10_formula
    · exact nativeHeat151Init11_formula
    · exact nativeHeat151Init12_formula
    · exact nativeHeat151Init13_formula
    · exact nativeHeat151Init14_formula
    · exact nativeHeat151Init15_formula
    · exact nativeHeat151Init16_formula
    · exact nativeHeat151Init17_formula
    · exact nativeHeat151Init18_formula
    · exact nativeHeat151Init19_formula
    · exact nativeHeat151Init20_formula
theorem nativeHeatStep_hBase_151_Gen : nativeHeatBaseGen 151 = nativeHeat151Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_151_Gen, nativeHeatStep_hInit_151_Gen, nativeHeat151Base_formula]

theorem nativeHeatStep_hFixed_151_Gen : nativeHeatFixedGen 151 = nativeHeat151Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_151_Gen, nativeHeatStep_hFr_151_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat151Fixed01_formula
    · exact nativeHeat151Fixed02_formula
    · exact nativeHeat151Fixed03_formula
    · exact nativeHeat151Fixed04_formula
    · exact nativeHeat151Fixed05_formula
    · exact nativeHeat151Fixed06_formula
    · exact nativeHeat151Fixed07_formula
    · exact nativeHeat151Fixed08_formula
    · exact nativeHeat151Fixed09_formula
    · exact nativeHeat151Fixed10_formula
    · exact nativeHeat151Fixed11_formula
    · exact nativeHeat151Fixed12_formula
    · exact nativeHeat151Fixed13_formula
    · exact nativeHeat151Fixed14_formula
    · exact nativeHeat151Fixed15_formula
    · exact nativeHeat151Fixed16_formula
    · exact nativeHeat151Fixed17_formula
    · exact nativeHeat151Fixed18_formula
    · exact nativeHeat151Fixed19_formula
    · exact nativeHeat151Fixed20_formula

theorem nativeHeatStep_chk_151_Gen :
    nativeHeatPassRootsOk nativeGap152Old nativeHeat151Frames nativeHeat151Coef nativeHeat151Fixed nativeHeat151Base 48 nativeHeat151Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_151_Gen : NativeHeatStepPassNum 151 := by
  refine nativeHeatStepPassNum_of_literals 151 nativeGap152Old nativeHeat151Frames (nativeHeatExpArg nativeGap152Old)
    nativeHeat151Exp nativeHeat151Coef nativeHeat151Fixed nativeHeat151Init nativeHeat151Base nativeHeatStep_hOld_151_Gen
    nativeHeatStep_hFr_151_Gen nativeHeatStep_hArg_151_Gen nativeHeatStep_hExp_151_Gen
    nativeHeatStep_hCoef_151_Gen nativeHeatStep_hFixed_151_Gen
    nativeHeatStep_hInit_151_Gen nativeHeatStep_hBase_151_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_151_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_151_Gen :
    nativeHeatY0Gen 151 = nativeShiftedFrame 1 (min nativeGap152Old.x nativeGap152Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_151_Gen, nativeHeatStep_hInd_151_Gen]

theorem nativeHeatStepFrameNum_151_Gen : NativeHeatStepFrameNum 151 := by
  have h1 := nativeHeatStep_hOld_151_Gen
  have h2 := nativeHeatStep_hInd_151_Gen
  have h3 := nativeHeatStep_hVar_151_Gen
  have h4 := nativeHeatStep_hQm_151_Gen
  have h5 := nativeHeatStep_hQN_151_Gen
  have h6 := nativeHeatStep_hY0_151_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_151_Gen : NativeHeatStepIndivNum 151 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 151 (by norm_num)) = nativeGap152Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_151_Gen]; exact nativeGap152Old_source
  · rw [hc, nativeHeatStep_hInd_151_Gen]; exact nativeGap152Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_151_Gen : nativeHeatY48Gen 151 = nativeHeat151Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_151_Gen, nativeHeatStep_hFr_151_Gen,
    nativeHeatStep_hCoef_151_Gen, nativeHeatStep_hFixed_151_Gen,
    nativeHeatStep_hBase_151_Gen]
  exact nativeHeat151All48

theorem nativeHeatResultGen_151 : nativeHeatResultGen 151 = nativeHeat151Result := by
  rw [← nativeHeat151Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_151_Gen, nativeHeatStep_hY0_151_Gen, nativeHeatStep_hExp_151_Gen,
    nativeHeatStep_hInit_151_Gen, nativeHeatStep_hFixed_151_Gen]

end ASDExplicitGamma.Native

end
