module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat070Complete
public import ASDExplicitGamma.Numerics.Native.Gap071Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_070_Gen : nativeHeatOldRowGen 70 = nativeGap071Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_070_Gen : nativeHeatIndividualGen 70 = nativeGap071Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_070_Gen : nativeHeatGenVariance 70 = nativeHeat070Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_070_Gen, nativeHeat070Variance_formula]

theorem nativeHeatStep_hSpec_070_Gen : nativeHeatGenSpectral 70 = nativeHeat070Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_070_Gen, nativeHeat070Variance_formula]

theorem nativeHeatStep_hQm_070_Gen : nativeHeatGenQm 70 = nativeHeat070Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_070_Gen, nativeHeatStep_hSpec_070_Gen,
    nativeHeat070Qm_formula]

theorem nativeHeatStep_hQN_070_Gen : nativeHeatQNGen 70 = nativeHeat070QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_070_Gen, nativeHeat070QN_formula]

theorem nativeHeatStep_hFr_070_Gen : nativeHeatFramesGen 70 = nativeHeat070Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_070_Gen, nativeHeatStep_hInd_070_Gen,
    nativeHeatStep_hVar_070_Gen, nativeHeatStep_hQN_070_Gen, nativeHeat070Frames_formula]

theorem nativeHeatStep_hArg_070_Gen : nativeHeatExpArgGen 70 = nativeHeatExpArg nativeGap071Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_070_Gen]

theorem nativeHeatStep_hExp_070_Gen : nativeHeatExpGen 70 = nativeHeat070Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_070_Gen, nativeHeat070Exp_formula]

theorem nativeHeatStep_hCoef_070_Gen : nativeHeatCoefGen 70 = nativeHeat070Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_070_Gen, nativeHeat070Coef_formula]

theorem nativeHeatStep_hInit_070_Gen : nativeHeatInitGen 70 = nativeHeat070Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_070_Gen, nativeHeatStep_hVar_070_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat070Init00_formula
    · exact nativeHeat070Init01_formula
    · exact nativeHeat070Init02_formula
    · exact nativeHeat070Init03_formula
    · exact nativeHeat070Init04_formula
    · exact nativeHeat070Init05_formula
    · exact nativeHeat070Init06_formula
    · exact nativeHeat070Init07_formula
    · exact nativeHeat070Init08_formula
    · exact nativeHeat070Init09_formula
    · exact nativeHeat070Init10_formula
    · exact nativeHeat070Init11_formula
    · exact nativeHeat070Init12_formula
    · exact nativeHeat070Init13_formula
    · exact nativeHeat070Init14_formula
    · exact nativeHeat070Init15_formula
    · exact nativeHeat070Init16_formula
    · exact nativeHeat070Init17_formula
    · exact nativeHeat070Init18_formula
    · exact nativeHeat070Init19_formula
    · exact nativeHeat070Init20_formula
theorem nativeHeatStep_hBase_070_Gen : nativeHeatBaseGen 70 = nativeHeat070Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_070_Gen, nativeHeatStep_hInit_070_Gen, nativeHeat070Base_formula]

theorem nativeHeatStep_hFixed_070_Gen : nativeHeatFixedGen 70 = nativeHeat070Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_070_Gen, nativeHeatStep_hFr_070_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat070Fixed01_formula
    · exact nativeHeat070Fixed02_formula
    · exact nativeHeat070Fixed03_formula
    · exact nativeHeat070Fixed04_formula
    · exact nativeHeat070Fixed05_formula
    · exact nativeHeat070Fixed06_formula
    · exact nativeHeat070Fixed07_formula
    · exact nativeHeat070Fixed08_formula
    · exact nativeHeat070Fixed09_formula
    · exact nativeHeat070Fixed10_formula
    · exact nativeHeat070Fixed11_formula
    · exact nativeHeat070Fixed12_formula
    · exact nativeHeat070Fixed13_formula
    · exact nativeHeat070Fixed14_formula
    · exact nativeHeat070Fixed15_formula
    · exact nativeHeat070Fixed16_formula
    · exact nativeHeat070Fixed17_formula
    · exact nativeHeat070Fixed18_formula
    · exact nativeHeat070Fixed19_formula
    · exact nativeHeat070Fixed20_formula

theorem nativeHeatStep_chk_070_Gen :
    nativeHeatPassRootsOk nativeGap071Old nativeHeat070Frames nativeHeat070Coef nativeHeat070Fixed nativeHeat070Base 48 nativeHeat070Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_070_Gen : NativeHeatStepPassNum 70 := by
  refine nativeHeatStepPassNum_of_literals 70 nativeGap071Old nativeHeat070Frames (nativeHeatExpArg nativeGap071Old)
    nativeHeat070Exp nativeHeat070Coef nativeHeat070Fixed nativeHeat070Init nativeHeat070Base nativeHeatStep_hOld_070_Gen
    nativeHeatStep_hFr_070_Gen nativeHeatStep_hArg_070_Gen nativeHeatStep_hExp_070_Gen
    nativeHeatStep_hCoef_070_Gen nativeHeatStep_hFixed_070_Gen
    nativeHeatStep_hInit_070_Gen nativeHeatStep_hBase_070_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_070_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_070_Gen :
    nativeHeatY0Gen 70 = nativeShiftedFrame 1 (min nativeGap071Old.x nativeGap071Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_070_Gen, nativeHeatStep_hInd_070_Gen]

theorem nativeHeatStepFrameNum_070_Gen : NativeHeatStepFrameNum 70 := by
  have h1 := nativeHeatStep_hOld_070_Gen
  have h2 := nativeHeatStep_hInd_070_Gen
  have h3 := nativeHeatStep_hVar_070_Gen
  have h4 := nativeHeatStep_hQm_070_Gen
  have h5 := nativeHeatStep_hQN_070_Gen
  have h6 := nativeHeatStep_hY0_070_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_070_Gen : NativeHeatStepIndivNum 70 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 70 (by norm_num)) = nativeGap071Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_070_Gen]; exact nativeGap071Old_source
  · rw [hc, nativeHeatStep_hInd_070_Gen]; exact nativeGap071Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_070_Gen : nativeHeatY48Gen 70 = nativeHeat070Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_070_Gen, nativeHeatStep_hFr_070_Gen,
    nativeHeatStep_hCoef_070_Gen, nativeHeatStep_hFixed_070_Gen,
    nativeHeatStep_hBase_070_Gen]
  exact nativeHeat070All48

theorem nativeHeatResultGen_070 : nativeHeatResultGen 70 = nativeHeat070Result := by
  rw [← nativeHeat070Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_070_Gen, nativeHeatStep_hY0_070_Gen, nativeHeatStep_hExp_070_Gen,
    nativeHeatStep_hInit_070_Gen, nativeHeatStep_hFixed_070_Gen]

end ASDExplicitGamma.Native

end
