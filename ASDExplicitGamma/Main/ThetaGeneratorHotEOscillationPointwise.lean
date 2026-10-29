module

public import ASDExplicitGamma.Main.ThetaGeneratorHotTrialExpectationsDrop
public import ASDExplicitGamma.Main.ThetaGeneratorMixedBridgeLocalCore
public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeA
public import ASDExplicitGamma.Main.LoadsAndSlopes
public import ASDExplicitGamma.Main.SourcePrefixGates
public import ASDExplicitGamma.Native.SourceRowsInterface
public import ASDExplicitGamma.Inverse.SourceInterfaceRows
public import ASDExplicitGamma.Scalar.MixedSourceCarriers
public import ASDExplicitGamma.Inverse.MixedBridgeConclusion
public import ASDExplicitGamma.Inverse.MixedBridgeLocalTheta
public import ASDExplicitGamma.Inverse.MixedBridgeLocalWeightedTheta
public import ASDExplicitGamma.Inverse.MixedBridgeSharpSlope
public import ASDExplicitGamma.Numerics.Native.Source5
public import ASDExplicitGamma.Main.AffineObserverFrame
public import ASDExplicitGamma.Inverse.MixedBridgeLocalCorrector
public import ASDExplicitGamma.Inverse.ParentGapRare
public import ASDExplicitGamma.Inverse.RawTraceHistory
public import ASDExplicitGamma.Native.OldSignedParentWeakBudgets
public import ASDExplicitGamma.Native.OldSignedSourceInverseSplit
public import ASDExplicitGamma.Main.ThetaGeneratorHotEOscillationPathwise
public import ASDExplicitGamma.Main.HotCoefficientId
public import ASDExplicitGamma.Main.HotPatchBank
public import ASDExplicitGamma.Main.HotPatchKa
public import ASDExplicitGamma.Main.HotPatchCorrectorSize
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsDrop
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsVl2

/-! ω-level domination of the hot oscillatory C-group row at the observer root
`originCube 2 (m + hobs)`:
`row ≤ 2 (k_a (B* Δ)^{1/2} + k_d (avg V_U²)^{1/2}) · (actual joint profile)`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response

noncomputable section

/-- The shell length `3^(m+1)` equals the depth-`hobs+5` cell scale times `3^6`. -/
theorem hot_scale_eq_Th (m : ℤ) (hobs : ℕ) :
    cubeScaleFactor (originCube 2 (m + hobs)) / (3 : ℝ) ^ (hobs + 5) * (3 : ℝ) ^ 6 =
      (q3ModelLength (m + 1)).1 := by
  rw [cubeScaleFactor_originCube]
  change (3 : ℝ) ^ (m + (hobs : ℤ)) / (3 : ℝ) ^ (hobs + 5) * (3 : ℝ) ^ 6 = (3 : ℝ) ^ (m + 1)
  rw [zpow_add₀ (by norm_num), zpow_add₀ (by norm_num), zpow_natCast]
  rw [pow_add]
  field_simp

theorem hot_cells_scale_Th (m : ℤ) (hobs : ℕ) :
    ∀ R ∈ descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5),
      cubeScaleFactor R * 3 ^ 6 ≤ (q3ModelLength (m + 1)).1 := by
  intro R hR
  rw [cubeScaleFactor_descendant_eq_div_pow hR]
  exact (hot_scale_eq_Th m hobs).le

/-- Root-level hot coefficient of the actual insertion. -/
def hotRootCoefficient_Th (m : ℤ) (hobs : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    ResponseCoefficient (openCubeSet (originCube 2 (m + hobs))) :=
  mainAffineOpenResponseRestriction (originCube 2 (m + hobs))
    (modelInsertedScalar (closure (cubeSet (originCube 2 (m + hobs)))) m t ω)

/-- The hot oscillatory row as a function on the cutoff sample space. -/
def mainHotOscRow_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t b : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  hotOscRow_Th (originCube 2 (m + hobs)) (hobs + 5) M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1 (hotRootCoefficient_Th m hobs t ω) b
    (q3ModelLength (m + 1))

theorem main_hot_osc_row_le_dom_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (b : ℝ) (ω : Cutoff.CutoffSample 2) :
    mainHotOscRow_Th M m hobs t b ω ≤
      2 * ((mainKa (b ^ 2) * Real.sqrt (mixedBridgeBstar M m t ω *
            mainHotDropObs_Th M m hobs t ω) +
          mainKd (b ^ 2) * Real.sqrt (descendantsAverage (originCube 2 (m + hobs)) (hobs + 5)
            (fun U => mixedBridgeVLocal_Th M m U t ω ^ 2))) *
        mainEoscDepthFiveActualJointProfileHot (q3ModelLength (m + 1)) hobs M m t b ω) := by
  classical
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar_characterization M m).1
  have hB : ∀ (U : TriadicCube 2)
      (hU : U ∈ descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5)),
      oldSignedInverseHistory U (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ)
        (oldSignedCellCoefficient (originCube 2 (m + hobs)) U
          (openCubeSet_subset_of_mem_descendantsAtDepth hU)
          (hotRootCoefficient_Th m hobs t ω))) ≤ mixedBridgeBstar M m t ω := by
    intro U hU
    have h1 := (old_signed_cell_histories (originCube 2 (m + hobs)) U
      (openCubeSet_subset_of_mem_descendantsAtDepth hU) M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos hσ (hotRootCoefficient_Th m hobs t ω)).1
    rw [h1]
    exact hot_cell_history_le_bstar M m hobs h40 t ht ω U hU
  have hpath := hot_osc_row_pathwise_Th (m + hobs) (hobs + 5) M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos hσ (hotRootCoefficient_Th m hobs t ω) b (q3ModelLength (m + 1))
    (hot_cells_scale_Th m hobs) (mixedBridgeBstar M m t ω) hB
  have hka := hot_source_multiplier_eq_mainKa m hobs b
  let Q := originCube 2 (m + hobs)
  have hroot : Q ∈ descendantsAtDepth Q 0 := by
    simp only [descendantsAtDepth_zero, Finset.mem_singleton]
  have hcells : descendantsAverage Q (hobs + 5) (fun U => rawCubeFourLoadTrace M m U t ω) =
      descendantsAverage Q (hobs + 5) (fun U => traceDefect (openCubeSet U)
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (hotRootCoefficient_Th m hobs t ω)) 1) := by
    refine main_hot_descendants_average_congr_Th _ _ _ _ ?_
    intro U hU
    exact main_hot_trace_eq_frame_trace_obs_Th M m Q t ω (hobs + 5) U hU
  have hr : rawCubeFourLoadTrace M m Q t ω = traceDefect (openCubeSet Q)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (hotRootCoefficient_Th m hobs t ω)) 1 :=
    main_hot_trace_eq_frame_trace_obs_Th M m Q t ω 0 Q hroot
  have e_drop : descendantsAverage Q (hobs + 5) (fun U => traceDefect (openCubeSet U)
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (hotRootCoefficient_Th m hobs t ω)) 1) -
      traceDefect (openCubeSet Q) (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ) (hotRootCoefficient_Th m hobs t ω)) 1 =
      mainHotDropObs_Th M m hobs t ω := by
    unfold mainHotDropObs_Th
    rw [hcells, hr]
  have e_K : ∑ c : BlockCoord 2, lemmaVTiledWeakEnergy Q (hobs + 5)
        (hotGluedCorrector Q (hobs + 5) M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ
          (hotRootCoefficient_Th m hobs t ω) (blockBasis c)).toH1Function.grad =
      descendantsAverage Q (hobs + 5) (fun U => mixedBridgeVLocal_Th M m U t ω ^ 2) := by
    rw [hot_corrector_tiled_eq_primal_sizes Q (hobs + 5) M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos hσ (hotRootCoefficient_Th m hobs t ω)]
    refine Eq.trans (congrArg (oldSignedCellAverage Q (hobs + 5)) (funext fun U => ?_))
      (old_signed_cell_average_eq_descendantsAverage Q (hobs + 5)
        (fun U => mixedBridgeVLocal_Th M m U t ω ^ 2))
    have hc := hot_cell_coefficient_eq M Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) m t ω
    unfold mixedBridgeVLocal_Th
    simp only [hotRootCoefficient_Th]
    rw [hc]
  have e_prof : Real.sqrt (descendantsAverage Q (hobs + 5) (fun U =>
        mainOldJointOscillationProfile Q U M.nu (Annealed.sigmaBar M m : ℝ)
          (hotRootCoefficient_Th m hobs t ω) b (q3ModelLength (m + 1)) ^ 2)) =
      mainEoscDepthFiveActualJointProfileHot (q3ModelLength (m + 1)) hobs M m t b ω := by
    unfold mainEoscDepthFiveActualJointProfileHot hotRootCoefficient_Th
    rw [hot_root_coefficient_eq_skew M Q m t ω]
  rw [hka, e_drop, e_K, e_prof] at hpath
  exact hpath

end

end ASDExplicitGamma.Main
