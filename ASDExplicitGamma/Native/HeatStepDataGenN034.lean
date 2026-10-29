module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat034Complete
public import ASDExplicitGamma.Numerics.Native.Gap035Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_034_Gen : nativeHeatOldRowGen 34 = nativeGap035Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_034_Gen : nativeHeatIndividualGen 34 = nativeGap035Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_034_Gen : nativeHeatGenVariance 34 = nativeHeat034Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_034_Gen, nativeHeat034Variance_formula]

theorem nativeHeatStep_hSpec_034_Gen : nativeHeatGenSpectral 34 = nativeHeat034Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_034_Gen, nativeHeat034Variance_formula]

theorem nativeHeatStep_hQm_034_Gen : nativeHeatGenQm 34 = nativeHeat034Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_034_Gen, nativeHeatStep_hSpec_034_Gen,
    nativeHeat034Qm_formula]

theorem nativeHeatStep_hQN_034_Gen : nativeHeatQNGen 34 = nativeHeat034QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_034_Gen, nativeHeat034QN_formula]

theorem nativeHeatStep_hFr_034_Gen : nativeHeatFramesGen 34 = nativeHeat034Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_034_Gen, nativeHeatStep_hInd_034_Gen,
    nativeHeatStep_hVar_034_Gen, nativeHeatStep_hQN_034_Gen, nativeHeat034Frames_formula]

theorem nativeHeatStep_hArg_034_Gen : nativeHeatExpArgGen 34 = nativeHeatExpArg nativeGap035Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_034_Gen]

theorem nativeHeatStep_hExp_034_Gen : nativeHeatExpGen 34 = nativeHeat034Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_034_Gen, nativeHeat034Exp_formula]

theorem nativeHeatStep_hCoef_034_Gen : nativeHeatCoefGen 34 = nativeHeat034Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_034_Gen, nativeHeat034Coef_formula]

theorem nativeHeatStep_hInit_034_Gen : nativeHeatInitGen 34 = nativeHeat034Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_034_Gen, nativeHeatStep_hVar_034_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat034Init00_formula
    · exact nativeHeat034Init01_formula
    · exact nativeHeat034Init02_formula
    · exact nativeHeat034Init03_formula
    · exact nativeHeat034Init04_formula
    · exact nativeHeat034Init05_formula
    · exact nativeHeat034Init06_formula
    · exact nativeHeat034Init07_formula
    · exact nativeHeat034Init08_formula
    · exact nativeHeat034Init09_formula
    · exact nativeHeat034Init10_formula
    · exact nativeHeat034Init11_formula
    · exact nativeHeat034Init12_formula
    · exact nativeHeat034Init13_formula
    · exact nativeHeat034Init14_formula
    · exact nativeHeat034Init15_formula
    · exact nativeHeat034Init16_formula
    · exact nativeHeat034Init17_formula
    · exact nativeHeat034Init18_formula
    · exact nativeHeat034Init19_formula
    · exact nativeHeat034Init20_formula
theorem nativeHeatStep_hBase_034_Gen : nativeHeatBaseGen 34 = nativeHeat034Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_034_Gen, nativeHeatStep_hInit_034_Gen, nativeHeat034Base_formula]

theorem nativeHeatStep_hFixed_034_Gen : nativeHeatFixedGen 34 = nativeHeat034Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_034_Gen, nativeHeatStep_hFr_034_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat034Fixed01_formula
    · exact nativeHeat034Fixed02_formula
    · exact nativeHeat034Fixed03_formula
    · exact nativeHeat034Fixed04_formula
    · exact nativeHeat034Fixed05_formula
    · exact nativeHeat034Fixed06_formula
    · exact nativeHeat034Fixed07_formula
    · exact nativeHeat034Fixed08_formula
    · exact nativeHeat034Fixed09_formula
    · exact nativeHeat034Fixed10_formula
    · exact nativeHeat034Fixed11_formula
    · exact nativeHeat034Fixed12_formula
    · exact nativeHeat034Fixed13_formula
    · exact nativeHeat034Fixed14_formula
    · exact nativeHeat034Fixed15_formula
    · exact nativeHeat034Fixed16_formula
    · exact nativeHeat034Fixed17_formula
    · exact nativeHeat034Fixed18_formula
    · exact nativeHeat034Fixed19_formula
    · exact nativeHeat034Fixed20_formula

theorem nativeHeatStep_chk_034_Gen :
    nativeHeatPassRootsOk nativeGap035Old nativeHeat034Frames nativeHeat034Coef nativeHeat034Fixed nativeHeat034Base 48 nativeHeat034Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_034_Gen : NativeHeatStepPassNum 34 := by
  refine nativeHeatStepPassNum_of_literals 34 nativeGap035Old nativeHeat034Frames (nativeHeatExpArg nativeGap035Old)
    nativeHeat034Exp nativeHeat034Coef nativeHeat034Fixed nativeHeat034Init nativeHeat034Base nativeHeatStep_hOld_034_Gen
    nativeHeatStep_hFr_034_Gen nativeHeatStep_hArg_034_Gen nativeHeatStep_hExp_034_Gen
    nativeHeatStep_hCoef_034_Gen nativeHeatStep_hFixed_034_Gen
    nativeHeatStep_hInit_034_Gen nativeHeatStep_hBase_034_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_034_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_034_Gen :
    nativeHeatY0Gen 34 = nativeShiftedFrame 1 (min nativeGap035Old.x nativeGap035Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_034_Gen, nativeHeatStep_hInd_034_Gen]

theorem nativeHeatStepFrameNum_034_Gen : NativeHeatStepFrameNum 34 := by
  have h1 := nativeHeatStep_hOld_034_Gen
  have h2 := nativeHeatStep_hInd_034_Gen
  have h3 := nativeHeatStep_hVar_034_Gen
  have h4 := nativeHeatStep_hQm_034_Gen
  have h5 := nativeHeatStep_hQN_034_Gen
  have h6 := nativeHeatStep_hY0_034_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_034_Gen : NativeHeatStepIndivNum 34 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 34 (by norm_num)) = nativeGap035Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_034_Gen]; exact nativeGap035Old_source
  · rw [hc, nativeHeatStep_hInd_034_Gen]; exact nativeGap035Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_034_Gen : nativeHeatY48Gen 34 = nativeHeat034Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_034_Gen, nativeHeatStep_hFr_034_Gen,
    nativeHeatStep_hCoef_034_Gen, nativeHeatStep_hFixed_034_Gen,
    nativeHeatStep_hBase_034_Gen]
  exact nativeHeat034All48

theorem nativeHeatResultGen_034 : nativeHeatResultGen 34 = nativeHeat034Result := by
  rw [← nativeHeat034Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_034_Gen, nativeHeatStep_hY0_034_Gen, nativeHeatStep_hExp_034_Gen,
    nativeHeatStep_hInit_034_Gen, nativeHeatStep_hFixed_034_Gen]

end ASDExplicitGamma.Native

end
