/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackGapPair
public import ASDExplicitGamma.Scalar.SmoothFeedbackResponse
public import ASDExplicitGamma.Scalar.SmoothFeedbackJointCell
public import ASDExplicitGamma.Scalar.SmoothFeedbackGammaTranslation
public import ASDExplicitGamma.Scalar.SmoothFeedbackGammaTheta
public import ASDExplicitGamma.Model.CutoffAction

/-! Annealed (expectation over the OLD law) unweighted bounds for the actual
cell charges `A_pair`, `P_K`, `P_D` of the smooth-feedback estimate, with the
cell-dependent means of the actual shell loads. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native
open Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Main
attribute [local irreducible] Homogenization.descendantsAtDepth
open scoped BigOperators

noncomputable section

/-- The coarse matrix of the restricted parent OLD coefficient on a child
cell is the actual framed response `A_U` of that child. -/
theorem smooth_feedback_cell_coarse_eq_response
    (M : ABKModel 2) (m : ℤ) (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (ω : Cutoff.CutoffSample 2) :
    coarseBlockMatrix (openCubeSet U)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (oldSignedCellCoefficient Q U hU (oldCutoffSkewCoefficient m Q ω))) =
      smoothFeedbackCellA M m U ω := by
  rw [smooth_feedback_cell_coefficient_restrict m Q U hU ω]
  have hCube : coarseBlockMatrix (cubeSet U)
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ) (smoothFeedbackCellCubeCoefficient m U ω)) =
      smoothFeedbackCellA M m U ω := by
    have hframe := Variational.response_coarseMatrix_frame_eq
      (measurableSet_cubeSet U) M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar M m).property (smoothFeedbackCellCubeCoefficient m U ω)
    rw [hframe, coarseBlockMatrix_congr_of_ae_eq
      (smooth_feedback_cube_physical_coefficient M m U ω)]
    rfl
  calc
    _ = coarseBlockMatrix (openCubeSet U)
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ) (smoothFeedbackCellCubeCoefficient m U ω)) :=
      coarseBlockMatrix_congr_of_ae_eq
        (smooth_feedback_open_frame_coefficients_ae M m U ω)
    _ = coarseBlockMatrix (cubeSet U)
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ) (smoothFeedbackCellCubeCoefficient m U ω)) :=
      (Variational.cube_coarseMatrix_eq_open U _).symm
    _ = _ := hCube

theorem smooth_feedback_block_top_quadratic (A : BlockMat 2) (w : Vec 2) :
    blockVecDot ((w, 0) : BlockVec 2) (blockMatVecMul A (w, 0)) =
      vecDot w (matVecMul A.upperLeft w) := by
  simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]

theorem smooth_feedback_block_bottom_quadratic (A : BlockMat 2) (w : Vec 2) :
    blockVecDot ((0, w) : BlockVec 2) (blockMatVecMul A (0, w)) =
      vecDot w (matVecMul A.lowerRight w) := by
  simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]

private theorem annealed_response_entry_integrable
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (i j : BlockCoord 2) :
    Integrable (fun ω => Cold.coldNativeResponse M m Q ω i j)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hT := Cold.coldNativeCellTrace_integrable M m Q
  have hmajor : Integrable
      (fun ω => Cold.coldNativeCellTrace M m Q ω + 2) μ :=
    hT.add (integrable_const 2)
  have hmeas : Measurable (fun ω => Cold.coldNativeResponse M m Q ω i j) :=
    (measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp (Cold.coldNativeResponse_measurable M m Q))
  refine hmajor.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  have hTnonneg := Cold.coldNativeCellTrace_nonneg M m Q ω
  have hspec := Cold.coldNativeResponse_spectral M m Q ω
  have hentry := Cold.matrix_entry_abs_le_trace_add_two
    (Cold.coldNativeResponse M m Q ω) hTnonneg hspec i j
  change ‖Cold.coldNativeResponse M m Q ω i j‖ ≤
    Cold.coldNativeCellTrace M m Q ω + 2
  rw [Real.norm_eq_abs]
  exact hentry

theorem smooth_feedback_cell_K_quad_integrable (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (w : Vec 2) :
    Integrable (fun ω => vecDot w (matVecMul (smoothFeedbackCellK M m Q ω) w))
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    Integrable (fun ω => vecDot w (matVecMul (smoothFeedbackCellD M m Q ω) w))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hKentry : ∀ i j : Fin 2,
      Integrable (fun ω => smoothFeedbackCellK M m Q ω i j) μ := by
    intro i j
    change Integrable
      (fun ω => Cold.coldNativeResponse M m Q ω (Sum.inl i) (Sum.inl j)) μ
    exact annealed_response_entry_integrable M m Q (Sum.inl i) (Sum.inl j)
  have hDentry : ∀ i j : Fin 2,
      Integrable (fun ω => smoothFeedbackCellD M m Q ω i j) μ := by
    intro i j
    change Integrable
      (fun ω => Cold.coldNativeResponse M m Q ω (Sum.inr i) (Sum.inr j)) μ
    exact annealed_response_entry_integrable M m Q (Sum.inr i) (Sum.inr j)
  let P : Mat 2 := fun i j => w i * w j
  have hrepr (A : Mat 2) :
      vecDot w (matVecMul A w) = Cold.matrixFrobeniusInner P A := by
    simp only [vecDot, matVecMul, Cold.matrixFrobeniusInner, P, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  constructor
  · have hinner : Integrable
        (fun ω => Cold.matrixFrobeniusInner P (smoothFeedbackCellK M m Q ω)) μ := by
      unfold Cold.matrixFrobeniusInner
      exact integrable_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun j _ => (hKentry i j).const_mul (P i j)))
    exact hinner.congr (Filter.Eventually.of_forall fun ω => (hrepr _).symm)
  · have hinner : Integrable
        (fun ω => Cold.matrixFrobeniusInner P (smoothFeedbackCellD M m Q ω)) μ := by
      unfold Cold.matrixFrobeniusInner
      exact integrable_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun j _ => (hDentry i j).const_mul (P i j)))
    exact hinner.congr (Filter.Eventually.of_forall fun ω => (hrepr _).symm)

/-- Expectation of a finite family of cell averages, bounded cellwise. -/
theorem annealed_family_cell_mean_le
    {Ω' ι : Type*} [MeasurableSpace Ω'] {ℙ : Measure Ω'}
    (Q : TriadicCube 2) (r : ℕ) (S : Finset ι)
    (g : ι → Cold.SquareCells Q r → Ω' → ℝ) (c : ι → Cold.SquareCells Q r → ℝ)
    (hint : ∀ i C, Integrable (g i C) ℙ)
    (hle : ∀ i C, (∫ ω, g i C ω ∂ℙ) ≤ c i C) :
    (∫ ω, ∑ i ∈ S, Cold.squareCellMean Q r (fun C => g i C ω) ∂ℙ) ≤
      ∑ i ∈ S, Cold.squareCellMean Q r (c i) := by
  rw [integral_finsetSum S (fun i _ => Cold.integrable_squareCellMean Q r
    (fun C => hint i C))]
  apply Finset.sum_le_sum
  intro i _
  rw [Cold.integral_squareCellMean Q r (fun C => hint i C)]
  exact Cold.squareCellMean_mono Q r (fun C => hle i C)

/-- Annealed unweighted bounds for the actual cell charges `A_pair`, `P_K`,
`P_D` on the physical cells, with the actual cell means of the finite family
of loads. The cap `a5` is the hypothesis `sup_U E T_U <= a5` of the source. -/
theorem smooth_feedback_annealed_cell_charges
    {ι : Type*} (S : Finset ι)
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (depth : ℕ)
    (f : ι → Vec 2 → Vec 2) {a5 : ℝ}
    (hTcap : ∀ U : TriadicCube 2, U ∈ descendantsAtDepth Q depth →
      (∫ ω, smoothFeedbackCellT M m U ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ a5) :
    let σ : ℝ := Annealed.sigmaBar M m
    let Wmean2 : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      vecNormSq (fun j => cubeAverage U.val (fun x => f i x j)))
    let Mat : (ω : Cutoff.CutoffSample 2) → OldSignedCellIndex Q depth → BlockMat 2 :=
      fun ω U => coarseBlockMatrix (openCubeSet U.val)
        (responseFramePlanarCoefficientField M.nu σ
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
            (oldCutoffSkewCoefficient m Q ω)))
    let mean : ι → OldSignedCellIndex Q depth → Vec 2 := fun i U j =>
      cubeAverage U.val (fun x => f i x j)
    let Apair : Cutoff.CutoffSample 2 → ℝ := fun ω => ∑ i ∈ S,
      oldSignedCellAverage Q depth (fun U =>
        blockVecDot ((mean i U, 0) : BlockVec 2) (blockMatVecMul (Mat ω U) (mean i U, 0)) +
          blockVecDot ((0, mean i U) : BlockVec 2) (blockMatVecMul (Mat ω U) (0, mean i U)) -
          2 * vecNormSq (mean i U))
    let PK : Cutoff.CutoffSample 2 → ℝ := fun ω => ∑ i ∈ S,
      oldSignedCellAverage Q depth (fun U =>
        blockVecDot ((mean i U, 0) : BlockVec 2) (blockMatVecMul (Mat ω U) (mean i U, 0)))
    let PD : Cutoff.CutoffSample 2 → ℝ := fun ω => ∑ i ∈ S,
      oldSignedCellAverage Q depth (fun U =>
        blockVecDot ((0, mean i U) : BlockVec 2) (blockMatVecMul (Mat ω U) (0, mean i U)))
    (∫ ω, Apair ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ (a5 / 2) * Wmean2 ∧
    (∫ ω, PK ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ (1 + a5 / 2) * Wmean2 ∧
    (∫ ω, PD ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ (1 + a5 / 2) * Wmean2 := by
  classical
  intro σ Wmean2 Mat mean Apair PK PD
  have hMat (ω : Cutoff.CutoffSample 2) (U : OldSignedCellIndex Q depth) :
      Mat ω U = smoothFeedbackCellA M m U.val ω :=
    smooth_feedback_cell_coarse_eq_response M m Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) ω
  have hWm : Wmean2 = ∑ i ∈ S, Cold.squareCellMean Q depth (fun U =>
      vecNormSq (mean i U)) := rfl
  have hKq (i : ι) (U : OldSignedCellIndex Q depth) (ω : Cutoff.CutoffSample 2) :
      blockVecDot ((mean i U, 0) : BlockVec 2) (blockMatVecMul (Mat ω U) (mean i U, 0)) =
        vecDot (mean i U) (matVecMul (smoothFeedbackCellK M m U.val ω) (mean i U)) := by
    rw [hMat, smooth_feedback_block_top_quadratic]
    rfl
  have hDq (i : ι) (U : OldSignedCellIndex Q depth) (ω : Cutoff.CutoffSample 2) :
      blockVecDot ((0, mean i U) : BlockVec 2) (blockMatVecMul (Mat ω U) (0, mean i U)) =
        vecDot (mean i U) (matVecMul (smoothFeedbackCellD M m U.val ω) (mean i U)) := by
    rw [hMat, smooth_feedback_block_bottom_quadratic]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · have hfun : Apair = fun ω => ∑ i ∈ S, Cold.squareCellMean Q depth (fun U =>
        smoothFeedbackPairCharge M m U.val (mean i U) ω) := by
      funext ω
      apply Finset.sum_congr rfl
      intro i _
      unfold Cold.squareCellMean oldSignedCellAverage
      congr 1
      apply Finset.sum_congr rfl
      intro U _
      show _ = _
      simp only []
      rw [hKq i U ω, hDq i U ω]
      rfl
    rw [hfun]
    refine (annealed_family_cell_mean_le Q depth S _
      (fun i U => (a5 / 2) * vecNormSq (mean i U))
      (fun i U => smooth_feedback_cell_pair_charge_integrable M m U.val (mean i U))
      (fun i U => ?_)).trans ?_
    · rw [smooth_feedback_cell_mean_pair_quadratic]
      have h := hTcap U.val U.property
      have := mul_le_mul_of_nonneg_right h (vecNormSq_nonneg (mean i U))
      nlinarith [this]
    · rw [hWm, Finset.mul_sum]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro i _
      exact (Cold.squareCellMean_mul Q depth (a5 / 2) _)
  · have hfun : PK = fun ω => ∑ i ∈ S, Cold.squareCellMean Q depth (fun U =>
        vecDot (mean i U) (matVecMul (smoothFeedbackCellK M m U.val ω) (mean i U))) := by
      funext ω
      apply Finset.sum_congr rfl
      intro i _
      unfold Cold.squareCellMean oldSignedCellAverage
      congr 1
      apply Finset.sum_congr rfl
      intro U _
      exact hKq i U ω
    rw [hfun]
    refine (annealed_family_cell_mean_le Q depth S _
      (fun i U => (1 + a5 / 2) * vecNormSq (mean i U))
      (fun i U => (smooth_feedback_cell_K_quad_integrable M m U.val (mean i U)).1)
      (fun i U => (smooth_feedback_cell_mean_diagonal_quadratic_le M m U.val
        (mean i U) (hTcap U.val U.property)).1)).trans ?_
    · rw [hWm, Finset.mul_sum]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro i _
      exact (Cold.squareCellMean_mul Q depth (1 + a5 / 2) _)
  · have hfun : PD = fun ω => ∑ i ∈ S, Cold.squareCellMean Q depth (fun U =>
        vecDot (mean i U) (matVecMul (smoothFeedbackCellD M m U.val ω) (mean i U))) := by
      funext ω
      apply Finset.sum_congr rfl
      intro i _
      unfold Cold.squareCellMean oldSignedCellAverage
      congr 1
      apply Finset.sum_congr rfl
      intro U _
      exact hDq i U ω
    rw [hfun]
    refine (annealed_family_cell_mean_le Q depth S _
      (fun i U => (1 + a5 / 2) * vecNormSq (mean i U))
      (fun i U => (smooth_feedback_cell_K_quad_integrable M m U.val (mean i U)).2)
      (fun i U => (smooth_feedback_cell_mean_diagonal_quadratic_le M m U.val
        (mean i U) (hTcap U.val U.property)).2)).trans ?_
    · rw [hWm, Finset.mul_sum]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro i _
      exact (Cold.squareCellMean_mul Q depth (1 + a5 / 2) _)

/-- The OLD law is translation invariant, so the annealed directional Gamma of a
physical cell equals that of the centred cell of the same scale. -/
theorem smooth_feedback_expected_gamma_translate_origin
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (e : Vec 2) :
    (∫ ω, smoothFeedbackCellDirectionalGamma M m Q e ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ ω, smoothFeedbackCellDirectionalGamma M m (originCube 2 Q.scale) e ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let z : Vec 2 := triadicCubeShift Q
  let G0 : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    smoothFeedbackCellDirectionalGamma M m (originCube 2 Q.scale) e ω
  have hfun : (fun ω => smoothFeedbackCellDirectionalGamma M m Q e ω) =
      fun ω => G0 ((MeasurableEquiv.vadd z : Cutoff.CutoffSample 2 ≃ᵐ
        Cutoff.CutoffSample 2) ω) := by
    funext ω
    exact smooth_feedback_cell_directional_gamma_translate_origin M m Q e ω
  rw [hfun]
  exact (MeasureTheory.measurePreserving_vadd z μ).integral_comp'
    (f := (MeasurableEquiv.vadd z : Cutoff.CutoffSample 2 ≃ᵐ Cutoff.CutoffSample 2)) G0

/-- Annealed `Theta^Gamma` bound on the actual physical cells of side `m-5`
inside `Q_{m+129}`: each cell is paid by the accepted `mainEnvelopeXi` row, with
the planar half factor. -/
theorem smooth_feedback_annealed_gamma
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N)
    {ι : Type*} (S : Finset ι) (f : ι → Vec 2 → Vec 2) :
    let Q : TriadicCube 2 := originCube 2 (m + 129)
    let xi : ℝ := mainEnvelopeXi
      ((q3ModelAmplitude M h (m + 1) /
        (Annealed.sigmaBar M m : ℝ)) ^ 2)
      M.gamma mainSourceInversePrefix (theta M) 0
    let Wmean2 : ℝ := ∑ i ∈ S, oldSignedCellAverage Q 134 (fun U =>
      vecNormSq (fun j => cubeAverage U.val (fun x => f i x j)))
    let ThetaGamma : Cutoff.CutoffSample 2 → ℝ := fun ω => ∑ i ∈ S,
      oldSignedCellAverage Q 134 (fun U =>
        smoothFeedbackCellDirectionalGamma M m U.val
          (fun j => cubeAverage U.val (fun x => f i x j)) ω)
    (∫ ω, ThetaGamma ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ (xi / 2) * Wmean2 := by
  classical
  intro Q xi Wmean2 ThetaGamma
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let O : TriadicCube 2 := originCube 2 (m - ((5 : ℕ) : ℤ))
  have hO : O ∈ descendantsAtDepth (originCube 2 m) 5 :=
    ASDExplicitGamma.Inverse.originCube_mem_descendantsAtDepth' 2 m 5
  have hrow := Main.main_envelope_xi_depth5_actual_law
    M h hM hγ N hpast m hm
  have hlocal := hrow 0 ⟨by norm_num, by norm_num⟩ O hO (0 : Fin 4)
  have hThetaInt : Integrable
      (fun ω : Cutoff.CutoffSample 2 => mixedOldTheta M m O 0 ω) μ := by
    simpa [μ] using hlocal.1
  have hIntO (e : Vec 2) : Integrable
      (fun ω => smoothFeedbackCellDirectionalGamma M m O e ω) μ :=
    smooth_feedback_directional_gamma_integrable_of_theta_integrable
      M hγ m O hO e hThetaInt
  have hscale (U : OldSignedCellIndex Q 134) : originCube 2 U.val.scale = O := by
    have hs := scale_eq_sub_of_mem_descendantsAtDepth U.property
    have : U.val.scale = m - ((5 : ℕ) : ℤ) := by
      rw [hs]
      simp only [Q, originCube]
      push_cast
      ring
    rw [this]
  have hIntU (U : OldSignedCellIndex Q 134) (e : Vec 2) : Integrable
      (fun ω => smoothFeedbackCellDirectionalGamma M m U.val e ω) μ := by
    have hfun : (fun ω => smoothFeedbackCellDirectionalGamma M m U.val e ω) =
        (fun ω => smoothFeedbackCellDirectionalGamma M m
            (originCube 2 U.val.scale) e ω) ∘
          (MeasurableEquiv.vadd (triadicCubeShift U.val) :
            Cutoff.CutoffSample 2 ≃ᵐ Cutoff.CutoffSample 2) := by
      funext ω
      exact smooth_feedback_cell_directional_gamma_translate_origin M m U.val e ω
    rw [hfun, hscale U]
    exact ((MeasureTheory.measurePreserving_vadd (triadicCubeShift U.val) μ
      ).integrable_comp_emb (MeasurableEquiv.vadd (triadicCubeShift U.val) :
        Cutoff.CutoffSample 2 ≃ᵐ Cutoff.CutoffSample 2).measurableEmbedding).2 (hIntO e)
  have hcell (U : OldSignedCellIndex Q 134) (e : Vec 2) :
      (∫ ω, smoothFeedbackCellDirectionalGamma M m U.val e ω ∂μ) ≤
        (xi / 2) * vecNormSq e := by
    rw [smooth_feedback_expected_gamma_translate_origin M m U.val e, hscale U]
    exact smooth_feedback_expected_directional_gamma_le_main_envelope_xi
      M h hM hγ N hpast m hm O hO e
  have hfun : ThetaGamma = fun ω => ∑ i ∈ S, Cold.squareCellMean Q 134 (fun U =>
      smoothFeedbackCellDirectionalGamma M m U.val
        (fun j => cubeAverage U.val (fun x => f i x j)) ω) := rfl
  rw [hfun]
  refine (annealed_family_cell_mean_le Q 134 S _
    (fun i U => (xi / 2) * vecNormSq (fun j => cubeAverage U.val (fun x => f i x j)))
    (fun i U => hIntU U _) (fun i U => hcell U _)).trans ?_
  apply le_of_eq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Cold.squareCellMean_mul Q 134 (xi / 2) _

end

end ASDExplicitGamma.Scalar
