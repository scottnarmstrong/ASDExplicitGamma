module

public import ASDExplicitGamma.Native.HeatStepNumLemmas
public import ASDExplicitGamma.Numerics.Native.Heat136Complete
public import ASDExplicitGamma.Numerics.Native.Gap137Certificate

/-! Generated per-`ns` numerics of the refined-child heat step (G). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native


theorem nativeHeatStep_hOld_136_Gen : nativeHeatOldRowGen 136 = nativeGap137Old := by
  unfold nativeHeatOldRowGen
  rfl

theorem nativeHeatStep_hInd_136_Gen : nativeHeatIndividualGen 136 = nativeGap137Individual := by
  unfold nativeHeatIndividualGen
  rfl

theorem nativeHeatStep_hVar_136_Gen : nativeHeatGenVariance 136 = nativeHeat136Variance := by
  unfold nativeHeatGenVariance
  rw [nativeHeatStep_hOld_136_Gen, nativeHeat136Variance_formula]

theorem nativeHeatStep_hSpec_136_Gen : nativeHeatGenSpectral 136 = nativeHeat136Spectral := by
  unfold nativeHeatGenSpectral
  rw [nativeHeatStep_hOld_136_Gen, nativeHeat136Variance_formula]

theorem nativeHeatStep_hQm_136_Gen : nativeHeatGenQm 136 = nativeHeat136Qm := by
  rw [nativeHeatGenQm_eq, nativeHeatStep_hVar_136_Gen, nativeHeatStep_hSpec_136_Gen,
    nativeHeat136Qm_formula]

theorem nativeHeatStep_hQN_136_Gen : nativeHeatQNGen 136 = nativeHeat136QN := by
  unfold nativeHeatQNGen
  rw [nativeHeatStep_hQm_136_Gen, nativeHeat136QN_formula]

theorem nativeHeatStep_hFr_136_Gen : nativeHeatFramesGen 136 = nativeHeat136Frames := by
  unfold nativeHeatFramesGen
  rw [nativeHeatStep_hOld_136_Gen, nativeHeatStep_hInd_136_Gen,
    nativeHeatStep_hVar_136_Gen, nativeHeatStep_hQN_136_Gen, nativeHeat136Frames_formula]

theorem nativeHeatStep_hArg_136_Gen : nativeHeatExpArgGen 136 = nativeHeatExpArg nativeGap137Old := by
  unfold nativeHeatExpArgGen
  rw [nativeHeatStep_hOld_136_Gen]

theorem nativeHeatStep_hExp_136_Gen : nativeHeatExpGen 136 = nativeHeat136Exp := by
  unfold nativeHeatExpGen
  rw [nativeHeatStep_hArg_136_Gen, nativeHeat136Exp_formula]

theorem nativeHeatStep_hCoef_136_Gen : nativeHeatCoefGen 136 = nativeHeat136Coef := by
  unfold nativeHeatCoefGen
  rw [nativeHeatStep_hExp_136_Gen, nativeHeat136Coef_formula]

theorem nativeHeatStep_hInit_136_Gen : nativeHeatInitGen 136 = nativeHeat136Init := by
  unfold nativeHeatInitGen nativeHeatInitial
  rw [nativeHeatStep_hQm_136_Gen, nativeHeatStep_hVar_136_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 21 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat136Init00_formula
    · exact nativeHeat136Init01_formula
    · exact nativeHeat136Init02_formula
    · exact nativeHeat136Init03_formula
    · exact nativeHeat136Init04_formula
    · exact nativeHeat136Init05_formula
    · exact nativeHeat136Init06_formula
    · exact nativeHeat136Init07_formula
    · exact nativeHeat136Init08_formula
    · exact nativeHeat136Init09_formula
    · exact nativeHeat136Init10_formula
    · exact nativeHeat136Init11_formula
    · exact nativeHeat136Init12_formula
    · exact nativeHeat136Init13_formula
    · exact nativeHeat136Init14_formula
    · exact nativeHeat136Init15_formula
    · exact nativeHeat136Init16_formula
    · exact nativeHeat136Init17_formula
    · exact nativeHeat136Init18_formula
    · exact nativeHeat136Init19_formula
    · exact nativeHeat136Init20_formula
theorem nativeHeatStep_hBase_136_Gen : nativeHeatBaseGen 136 = nativeHeat136Base := by
  unfold nativeHeatBaseGen
  rw [nativeHeatStep_hCoef_136_Gen, nativeHeatStep_hInit_136_Gen, nativeHeat136Base_formula]

theorem nativeHeatStep_hFixed_136_Gen : nativeHeatFixedGen 136 = nativeHeat136Fixed := by
  unfold nativeHeatFixedGen
  rw [nativeHeatStep_hOld_136_Gen, nativeHeatStep_hFr_136_Gen]
  apply nativeHeatStep_list_ext_getD
  · rw [List.length_map, List.length_range]
    rfl
  · intro i hi
    have hi' : i < 20 := by simpa using hi
    rw [nativeHeatStep_map_range_getD _ _ _ hi']
    interval_cases i
    · exact nativeHeat136Fixed01_formula
    · exact nativeHeat136Fixed02_formula
    · exact nativeHeat136Fixed03_formula
    · exact nativeHeat136Fixed04_formula
    · exact nativeHeat136Fixed05_formula
    · exact nativeHeat136Fixed06_formula
    · exact nativeHeat136Fixed07_formula
    · exact nativeHeat136Fixed08_formula
    · exact nativeHeat136Fixed09_formula
    · exact nativeHeat136Fixed10_formula
    · exact nativeHeat136Fixed11_formula
    · exact nativeHeat136Fixed12_formula
    · exact nativeHeat136Fixed13_formula
    · exact nativeHeat136Fixed14_formula
    · exact nativeHeat136Fixed15_formula
    · exact nativeHeat136Fixed16_formula
    · exact nativeHeat136Fixed17_formula
    · exact nativeHeat136Fixed18_formula
    · exact nativeHeat136Fixed19_formula
    · exact nativeHeat136Fixed20_formula

theorem nativeHeatStep_chk_136_Gen :
    nativeHeatPassRootsOk nativeGap137Old nativeHeat136Frames nativeHeat136Coef nativeHeat136Fixed nativeHeat136Base 48 nativeHeat136Frames.y = true := by
  decide +kernel

theorem nativeHeatStepPassNum_136_Gen : NativeHeatStepPassNum 136 := by
  refine nativeHeatStepPassNum_of_literals 136 nativeGap137Old nativeHeat136Frames (nativeHeatExpArg nativeGap137Old)
    nativeHeat136Exp nativeHeat136Coef nativeHeat136Fixed nativeHeat136Init nativeHeat136Base nativeHeatStep_hOld_136_Gen
    nativeHeatStep_hFr_136_Gen nativeHeatStep_hArg_136_Gen nativeHeatStep_hExp_136_Gen
    nativeHeatStep_hCoef_136_Gen nativeHeatStep_hFixed_136_Gen
    nativeHeatStep_hInit_136_Gen nativeHeatStep_hBase_136_Gen ?_
  unfold nativeHeatStepPassCheckLit
  rw [nativeHeatStep_chk_136_Gen]
  decide +kernel


theorem nativeHeatStep_hY0_136_Gen :
    nativeHeatY0Gen 136 = nativeShiftedFrame 1 (min nativeGap137Old.x nativeGap137Individual.1) := by
  unfold nativeHeatY0Gen
  rw [nativeHeatStep_hOld_136_Gen, nativeHeatStep_hInd_136_Gen]

theorem nativeHeatStepFrameNum_136_Gen : NativeHeatStepFrameNum 136 := by
  have h1 := nativeHeatStep_hOld_136_Gen
  have h2 := nativeHeatStep_hInd_136_Gen
  have h3 := nativeHeatStep_hVar_136_Gen
  have h4 := nativeHeatStep_hQm_136_Gen
  have h5 := nativeHeatStep_hQN_136_Gen
  have h6 := nativeHeatStep_hY0_136_Gen
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h4]; decide +kernel
  · unfold nativeHeatShiftArgGen; rw [h1, h2]; decide +kernel
  · rw [h6]; decide +kernel
  · rw [h3]; decide +kernel
  · rw [h5, h3]; decide +kernel
  · rw [h1]; decide +kernel
  · rw [h3]; decide +kernel

theorem nativeHeatStepIndivNum_136_Gen : NativeHeatStepIndivNum 136 (by norm_num) := by
  have hc : nativeConfiguredSystem (nativeHeatIndexGen 136 (by norm_num)) = nativeGap137Certificate := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc]; rfl
  · rw [nativeHeatStep_hOld_136_Gen]; exact nativeGap137Old_source
  · rw [hc, nativeHeatStep_hInd_136_Gen]; exact nativeGap137Individual_formula.symm
  · rw [hc]; decide +kernel

theorem nativeHeatStepY48_136_Gen : nativeHeatY48Gen 136 = nativeHeat136Y48 := by
  unfold nativeHeatY48Gen
  rw [nativeHeatStep_hOld_136_Gen, nativeHeatStep_hFr_136_Gen,
    nativeHeatStep_hCoef_136_Gen, nativeHeatStep_hFixed_136_Gen,
    nativeHeatStep_hBase_136_Gen]
  exact nativeHeat136All48

theorem nativeHeatResultGen_136 : nativeHeatResultGen 136 = nativeHeat136Result := by
  rw [← nativeHeat136Result_formula]
  unfold nativeHeatResultGen nativeHeatMeanGen
  rw [nativeHeatStepY48_136_Gen, nativeHeatStep_hY0_136_Gen, nativeHeatStep_hExp_136_Gen,
    nativeHeatStep_hInit_136_Gen, nativeHeatStep_hFixed_136_Gen]

end ASDExplicitGamma.Native

end
