module

public import ASDExplicitGamma.Main.ThetaGeneratorHotObsVl2
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsEnvelope
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsLocalRows
public import ASDExplicitGamma.Main.ThetaGeneratorHotEOscillationPointwise
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsSplit
public import ASDExplicitGamma.Main.ThetaGeneratorHotTrialExpectationsDrop
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsLocalHelpers
public import ASDExplicitGamma.Main.ThetaGeneratorHotTrialExpectationsSplit
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsDrop
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
public import ASDExplicitGamma.Main.ThetaGeneratorHotEOscillationNode
public import ASDExplicitGamma.Main.HotSourceEnergy
public import ASDExplicitGamma.Main.SourceSquare

/-! Node MA-E-SOURCE-SQUARE for the hot-patched trial at the observer root
`Q' = originCube 2 (m + hobs)` (`1 ≤ hobs ≤ 40`): the actual-law expectation of the source-square
group (patched-residual energy of the hot source) is at most `z²`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response

noncomputable section

/-- `K √u` is in `L²` with norm at most `K √C` when `u ≥ 0` is integrable with mean at most `C`. -/
theorem hot_memLp_const_mul_sqrt_Th {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (u : Ω → ℝ) (hu0 : ∀ ω, 0 ≤ u ω) (hu : Integrable u μ) (C K : ℝ) (hC : (∫ ω, u ω ∂μ) ≤ C)
    (hK : 0 ≤ K) :
    MemLp (fun ω => K * Real.sqrt (u ω)) 2 μ ∧
      lpNorm (fun ω => K * Real.sqrt (u ω)) 2 μ ≤ K * Real.sqrt C := by
  have hsq : MemLp (fun ω => Real.sqrt (u ω)) 2 μ :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hu.aestronglyMeasurable)).2
      (hu.congr (Filter.Eventually.of_forall fun ω => (Real.sq_sqrt (hu0 ω)).symm))
  have hmem : MemLp (fun ω => K * Real.sqrt (u ω)) 2 μ := hsq.const_mul K
  refine ⟨hmem, ?_⟩
  have hC0 : 0 ≤ C := (integral_nonneg hu0).trans hC
  have hint : (∫ ω, (K * Real.sqrt (u ω)) ^ 2 ∂μ) = K ^ 2 * ∫ ω, u ω ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [mul_pow, Real.sq_sqrt (hu0 ω)]
  have hsqb : lpNorm (fun ω => K * Real.sqrt (u ω)) 2 μ ^ 2 ≤ (K * Real.sqrt C) ^ 2 := by
    rw [ASDExplicitGamma.Gaussian.rio_lpNorm_two_sq hmem, hint, mul_pow, Real.sq_sqrt hC0]
    exact mul_le_mul_of_nonneg_left hC (sq_nonneg K)
  exact (sq_le_sq₀ (lpNorm_nonneg (f := fun ω => K * Real.sqrt (u ω)) (p := 2) (μ := μ))
    (mul_nonneg hK (Real.sqrt_nonneg C))).mp hsqb

/-- Per observer cell: `E[B* V_U²] ≤ β ξ`. -/
theorem hot_obs_cell_weighted_moment_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5)) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let v := (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2
    let xi := mainEnvelopeXi v M.gamma (theta M * mainSourceInversePrefix) (theta M) t
    Integrable (fun ω => mixedBridgeBstar M m t ω * mixedBridgeVLocal_Th M m U t ω ^ 2) μ ∧
      (∫ ω, mixedBridgeBstar M m t ω * mixedBridgeVLocal_Th M m U t ω ^ 2 ∂μ) ≤
        mainBeta * xi := by
  classical
  intro μ v xi
  have hscale := hot_obs_cell_scale_Th m hobs U hU
  have hroots := hot_obs_cell_mem_bank_roots_Th m hobs h40 U hU
  have hbs : mixedGlobalHistoryMax M m t = mixedBridgeBstar M m t :=
    funext fun ω => main_hot_bstar_eq_Th M m t ht ω
  have hEnv := main_envelope_xi_depth5_actual_law_Th M h hM hγ N hpast m hm t ht U hscale
    ⟨1, by norm_num⟩
  rw [hbs] at hEnv
  have hrows := mixed_bridge_local_pointwise_rows_Th M h hM hγ N hpast m hm t ht U hroots
  have hBm : Measurable (mixedBridgeBstar M m t) := parent_gap_bstar_measurable M m t
  have hVm := mixed_bridge_local_v2_measurable_Th M m U t
  have hbound : ∀ᵐ ω ∂μ, mixedBridgeBstar M m t ω * mixedBridgeVLocal_Th M m U t ω ^ 2 ≤
      mixedBridgeBstar M m t ω ^ 1 * mixedOldTheta M m U t ω := by
    filter_upwards [hrows] with ω hω
    have hT := raw_cube_four_load_trace_nonneg M m U t ⟨ht.1, ht.2⟩ ω
    have hV : mixedBridgeVLocal_Th M m U t ω ^ 2 ≤ mixedOldTheta M m U t ω := by
      have := hω.1
      have hb : 0 ≤ mainBetaOld * rawCubeFourLoadTrace M m U t ω :=
        mul_nonneg (by norm_num [mainBetaOld]) hT
      linarith
    rw [pow_one]
    exact mul_le_mul_of_nonneg_left hV (mixed_bridge_bstar_nonneg M m t ω)
  have hnonneg : ∀ ω, 0 ≤ mixedBridgeBstar M m t ω * mixedBridgeVLocal_Th M m U t ω ^ 2 :=
    fun ω => mul_nonneg (mixed_bridge_bstar_nonneg M m t ω) (sq_nonneg _)
  have hInt : Integrable (fun ω => mixedBridgeBstar M m t ω *
      mixedBridgeVLocal_Th M m U t ω ^ 2) μ := by
    refine hEnv.1.mono' (hBm.mul hVm).aestronglyMeasurable ?_
    filter_upwards [hbound] with ω hω
    rw [Real.norm_of_nonneg (hnonneg ω)]
    exact hω
  refine ⟨hInt, ?_⟩
  have := integral_mono_ae hInt hEnv.1 hbound
  simpa only [pow_one] using this.trans hEnv.2

/-- The cell-average of the squared hot source sizes, in `ω`-form. -/
theorem main_hot_source_size_sq_le_dom_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (b : ℝ) (ω : Cutoff.CutoffSample 2) :
    descendantsAverage (originCube 2 (m + hobs)) (hobs + 5) (fun U =>
      hotSourceSize (fun n P x => hotPatchSource (originCube 2 (m + hobs)) (hobs + 5)
        (hobs + 5) M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1 (hotRootCoefficient_Th m hobs t ω) b
        (q3ModelLength (m + 1)) n P x) U ^ 2) ≤
      (mainKa (b ^ 2) * Real.sqrt (mixedBridgeBstar M m t ω * mainHotDropObs_Th M m hobs t ω) +
        mainKd (b ^ 2) * Real.sqrt (descendantsAverage (originCube 2 (m + hobs)) (hobs + 5)
          (fun U => mixedBridgeVLocal_Th M m U t ω ^ 2))) ^ 2 := by
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
  obtain ⟨hs, hbound⟩ := hot_source_size_bound_of_cells (m + hobs) (hobs + 5) M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ (hotRootCoefficient_Th m hobs t ω) b
    (q3ModelLength (m + 1)) (hot_cells_scale_Th m hobs) (mixedBridgeBstar M m t ω) hB
  have hsrc := fun U hU => hot_source_cell_summable (m + hobs) (hobs + 5) M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ (hotRootCoefficient_Th m hobs t ω) b
    (q3ModelLength (m + 1)) (hot_cells_scale_Th m hobs) U hU
  have hs2 := hot_source_size_sq_average_Th (originCube 2 (m + hobs)) (hobs + 5) M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ (hotRootCoefficient_Th m hobs t ω) b
    (q3ModelLength (m + 1)) hsrc
  rw [hs2]
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
  rw [hka, e_drop, e_K] at hbound
  have hnn : 0 ≤ mainKa (b ^ 2) * Real.sqrt (mixedBridgeBstar M m t ω *
        mainHotDropObs_Th M m hobs t ω) + mainKd (b ^ 2) * Real.sqrt (descendantsAverage Q
        (hobs + 5) (fun U => mixedBridgeVLocal_Th M m U t ω ^ 2)) := by
    have hka0 : 0 ≤ mainKa (b ^ 2) := by unfold mainKa mainA2; positivity
    have := mainKd_nonneg (b ^ 2)
    positivity
  exact (Real.sqrt_le_iff.mp hbound).2

/-- The source-square group of the hot trial as a function of the cutoff sample. -/
def mainHotSourceSquareRow_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t b : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑' n : whiteBasisIndex, (hotPatchTrialTerms (originCube 2 (m + hobs)) (hobs + 5) M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
    (hotRootCoefficient_Th m hobs t ω) b (q3ModelLength (m + 1))).source n

theorem main_hot_source_square_row_le_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (b : ℝ) (ω : Cutoff.CutoffSample 2) :
    mainHotSourceSquareRow_Th M m hobs t b ω ≤
      (mainKa (b ^ 2) * Real.sqrt (mixedBridgeBstar M m t ω ^ 2 * mainHotDropObs_Th M m hobs t ω) +
        mainKd (b ^ 2) * Real.sqrt (mixedBridgeBstar M m t ω *
          descendantsAverage (originCube 2 (m + hobs)) (hobs + 5)
            (fun U => mixedBridgeVLocal_Th M m U t ω ^ 2))) ^ 2 := by
  classical
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar_characterization M m).1
  let Q := originCube 2 (m + hobs)
  let Bs := mixedBridgeBstar M m t ω
  let Dr := mainHotDropObs_Th M m hobs t ω
  let V2 := descendantsAverage Q (hobs + 5) (fun U => mixedBridgeVLocal_Th M m U t ω ^ 2)
  have hBs : 0 ≤ Bs := mixed_bridge_bstar_nonneg M m t ω
  have hDr : 0 ≤ Dr := (main_hot_drop_obs_pathwise_Th M m hobs t ω).2
  have hV2 : 0 ≤ V2 := by
    unfold V2 descendantsAverage
    exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun U _ => sq_nonneg _)
  have hbill := (hot_source_energy_bill (m + hobs) (hobs + 5) M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos hσ (hotRootCoefficient_Th m hobs t ω) b (q3ModelLength (m + 1))
    (hot_cells_scale_Th m hobs)).2
  have hcell : descendantsAverage Q (hobs + 5) (fun U =>
      oldSignedInverseHistory U (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ) (hotRootCoefficient_Th m hobs t ω)) *
        hotSourceSize (fun n P x => hotPatchSource Q (hobs + 5) (hobs + 5) M.nu
          (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ (hotRootCoefficient_Th m hobs t ω) b
          (q3ModelLength (m + 1)) n P x) U ^ 2) ≤
      descendantsAverage Q (hobs + 5) (fun U => Bs * hotSourceSize (fun n P x =>
        hotPatchSource Q (hobs + 5) (hobs + 5) M.nu
          (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ (hotRootCoefficient_Th m hobs t ω) b
          (q3ModelLength (m + 1)) n P x) U ^ 2) := by
    refine descendantsAverage_le fun U hU => ?_
    exact mul_le_mul_of_nonneg_right (hot_cell_history_le_bstar M m hobs h40 t ht ω U hU)
      (sq_nonneg _)
  rw [hot_desc_average_const_mul_Th] at hcell
  have hsize := main_hot_source_size_sq_le_dom_Th M m hobs h40 t ht b ω
  have hA := mul_le_mul_of_nonneg_left hsize hBs
  have hrow : mainHotSourceSquareRow_Th M m hobs t b ω ≤
      Bs * (mainKa (b ^ 2) * Real.sqrt (Bs * Dr) + mainKd (b ^ 2) * Real.sqrt V2) ^ 2 :=
    hbill.trans (hcell.trans hA)
  refine hrow.trans (le_of_eq ?_)
  have e1 : Real.sqrt (Bs ^ 2 * Dr) = Real.sqrt Bs ^ 2 * Real.sqrt Dr := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hBs]
    rw [← Real.sq_sqrt hBs]
    simp [Real.sqrt_sq (Real.sqrt_nonneg _)]
  have e2 : Real.sqrt (Bs * V2) = Real.sqrt Bs * Real.sqrt V2 := Real.sqrt_mul hBs _
  have e3 : Real.sqrt (Bs * Dr) = Real.sqrt Bs * Real.sqrt Dr := Real.sqrt_mul hBs _
  show Bs * _ = _
  rw [e1, e2, e3]
  have hs : Bs = Real.sqrt Bs ^ 2 := (Real.sq_sqrt hBs).symm
  nth_rewrite 1 [hs]
  ring

end

end ASDExplicitGamma.Main
