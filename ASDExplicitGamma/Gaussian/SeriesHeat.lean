/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.SeriesMoment
public import ASDExplicitGamma.Gaussian.FiniteHeat
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Hilbert-factorized Gaussian series and the Hessian trace

This file records the a.e. Hilbert-series version after applying a bounded map into a Banach
space, and proves absolute `L¹` summability of its Hessian trace under the stated polynomial
directional bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace ASDExplicitGamma.Gaussian

instance instStandardGaussianInfinitePiProbability :
    IsProbabilityMeasure standardGaussianInfinitePi := by
  dsimp [standardGaussianInfinitePi]
  infer_instance

/-- The Banach-valued version of the a.e. limit of the fast Hilbert-valued Gaussian subsequence. -/
noncomputable def gaussianSeriesLimitE {V E : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E) :
    (ℕ → ℝ) → E :=
  fun ω => T (gaussianSeriesLimit v hA ω)

theorem stronglyMeasurable_gaussianSeriesLimitE {V E : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E) :
    StronglyMeasurable (gaussianSeriesLimitE hA T) := by
  change StronglyMeasurable (fun ω => T (gaussianSeriesLimit v hA ω))
  exact T.continuous.comp_stronglyMeasurable (stronglyMeasurable_gaussianSeriesLimit v hA)

/-- The Banach-valued fast partial sums converge almost everywhere to the selected version. -/
theorem ae_tendsto_gaussianSeriesLimitE {V E : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E) :
    ∀ᵐ ω ∂standardGaussianInfinitePi,
      Tendsto (fun k => T (gaussianFastPartialSumSequence hA k ω)) atTop
        (𝓝 (gaussianSeriesLimitE hA T ω)) := by
  filter_upwards [ae_tendsto_gaussianSeriesLimit v hA] with ω hω
  exact T.continuous.continuousAt.tendsto.comp hω

theorem memLp_gaussianSeriesLimitE {V E : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : V →L[ℝ] E) {p : ℝ} (hp : 2 ≤ p) :
    MemLp (gaussianSeriesLimitE hA T) (ENNReal.ofReal p) standardGaussianInfinitePi := by
  change MemLp (fun ω => T (gaussianSeriesLimit v hA ω)) (ENNReal.ofReal p)
    standardGaussianInfinitePi
  exact (memLp_gaussianSeriesLimit v hA hp).continuousLinearMap_comp T

/-- The affine argument at which the limiting heat observable and its Hessian are evaluated. -/
noncomputable def gaussianSeriesHeatArgument {V E : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (x : E) (t : ℝ) : (ℕ → ℝ) → E :=
  fun ω => x + Real.sqrt t • gaussianSeriesLimitE hA T ω

/-- The finite-rank heat average evaluated on the countable product Gaussian space. -/
noncomputable def gaussianPartialSumHeatAverage {V E : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] {v : ℕ → V} (T : V →L[ℝ] E) (Φ : E → ℝ)
    (x : E) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ ω, Φ (x + Real.sqrt t • T (gaussianPartialSum v n ω))
    ∂standardGaussianInfinitePi

/-- Finite-coordinate expectations on the infinite product law reduce to the corresponding
finite product expectation. -/
theorem integral_gaussianPartialSum_eq_integral_piRange
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    {n : ℕ} {v : ℕ → V} {f : V → ℝ}
    (hf : AEStronglyMeasurable
      (fun z : (Finset.range n → ℝ) => f (∑ j, z j • v j))
      (Measure.pi (fun _ : Finset.range n => gaussianReal 0 1))) :
    ∫ ω, f (gaussianPartialSum v n ω) ∂standardGaussianInfinitePi =
      ∫ z, f (∑ j, z j • v j)
        ∂(Measure.pi (fun _ : Finset.range n => gaussianReal 0 1)) := by
  have hs (ω : ℕ → ℝ) : gaussianPartialSum v n ω =
      ∑ j : Finset.range n, ω j • v j := by
    calc
      gaussianPartialSum v n ω = ∑ j ∈ Finset.range n, ω j • v j := rfl
      _ = ∑ j ∈ (Finset.range n).attach, ω j • v j :=
        (Finset.sum_attach _ _).symm
      _ = ∑ j : Finset.range n, ω j • v j := by
        rw [Finset.attach_eq_univ]
  calc
    (∫ ω, f (gaussianPartialSum v n ω) ∂standardGaussianInfinitePi) =
        ∫ ω, f (∑ j : Finset.range n, ω j • v j)
          ∂Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1) := by
      simp only [standardGaussianInfinitePi]
      congr 1
      funext ω
      rw [hs]
    _ = ∫ z, f (∑ j, z j • v j)
          ∂(Measure.pi (fun _ : Finset.range n => gaussianReal 0 1)) :=
      integral_restrict_infinitePi (μ := fun _ : ℕ => gaussianReal 0 1) hf

/-- The finite-coordinate Gaussian law, reindexed from `Finset.range n` to `Fin n`. -/
theorem integral_gaussianPartialSum_eq_integral_standardPi
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] [SecondCountableTopology V]
    {n : ℕ} {v : ℕ → V} {f : V → ℝ} (hf : Continuous f) :
    ∫ ω, f (gaussianPartialSum v n ω) ∂standardGaussianInfinitePi =
      ∫ ξ, f (∑ i : Fin n,
        ξ i • v (((Finset.range n).equivFinOfCardEq (by simp)).symm i).1)
        ∂standardGaussianPi n := by
  let s : Finset ℕ := Finset.range n
  let e : s ≃ Fin n := s.equivFinOfCardEq (by simp [s])
  let fSub : (s → ℝ) → ℝ := fun z => f (∑ j, z j • v j.1)
  have hSubArg : Continuous (fun z : s → ℝ => ∑ j, z j • v j.1) := by
    let g : s → (s → ℝ) → V := fun j => fun z => z j • v j.1
    have hg (j : s) : Continuous (g j) := by
      dsimp [g]
      exact (continuous_apply j).smul continuous_const
    change Continuous (fun z => ∑ j ∈ Finset.univ, g j z)
    exact continuous_finsetSum Finset.univ (fun j hj => hg j)
  have hSubCont : Continuous fSub := by
    change Continuous (f ∘ fun z : s → ℝ => ∑ j, z j • v j.1)
    exact hf.comp hSubArg
  have hSubMeas : AEStronglyMeasurable fSub
      (Measure.pi (fun _ : s => gaussianReal 0 1)) := hSubCont.aestronglyMeasurable
  rw [integral_gaussianPartialSum_eq_integral_piRange hSubMeas]
  let hmp := measurePreserving_piCongrLeft
    (μ := fun _ : Fin n => gaussianReal 0 1) e
  let fFin : (Fin n → ℝ) → ℝ := fun ξ =>
    f (∑ i : Fin n, ξ i • v ((e.symm i).1))
  have hFinCont : Continuous fFin := by
    let g : Fin n → (Fin n → ℝ) → V := fun i => fun ξ => ξ i • v ((e.symm i).1)
    have hg (i : Fin n) : Continuous (g i) := by
      dsimp [g]
      exact (continuous_apply i).smul continuous_const
    change Continuous (f ∘ fun ξ : Fin n → ℝ => ∑ i ∈ Finset.univ, g i ξ)
    exact hf.comp (continuous_finsetSum Finset.univ (fun i hi => hg i))
  calc
    (∫ z, fSub z ∂(Measure.pi (fun _ : s => gaussianReal 0 1))) =
        ∫ ξ, fFin ξ ∂(Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
      calc
        _ = ∫ z, fFin (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e z)
            ∂(Measure.pi (fun _ : s => gaussianReal 0 1)) := by
              apply integral_congr_ae
              filter_upwards [] with z
              dsimp [fSub, fFin, MeasurableEquiv.piCongrLeft]
              simp [Equiv.piCongrLeft_apply]
              congr 1
              simpa only [Finset.attach_eq_univ] using
                (Equiv.sum_comp e.symm (fun j : s => z j • v j.1)).symm
        _ = _ := hmp.integral_comp' fFin
    _ = ∫ ξ, f (∑ i : Fin n,
        ξ i • v (((Finset.range n).equivFinOfCardEq (by simp)).symm i).1)
        ∂standardGaussianPi n := by
      rfl

/-- Polynomial growth of the second derivative in directional form. -/
def HasPolynomiallyBoundedSecondDirectionalDerivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ y w : E,
    |secondDirectionalDerivative Φ y w| ≤ C * (1 + ‖y‖) ^ d * ‖w‖ ^ 2

/-- Polynomial growth bounds for a `C²` observable and its first two Fréchet derivatives. The
last clause writes the operator norm bound for `D² Φ` on a pair of directions. -/
def HasPolynomiallyBoundedC2Derivatives {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → ℝ) : Prop :=
  ContDiff ℝ 2 Φ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ,
    (∀ y, |Φ y| ≤ C * (1 + ‖y‖) ^ d) ∧
    (∀ y, ‖fderiv ℝ Φ y‖ ≤ C * (1 + ‖y‖) ^ d) ∧
    ∀ y u w, |fderiv ℝ (fun z => fderiv ℝ Φ z w) y u| ≤
      C * (1 + ‖y‖) ^ d * ‖u‖ * ‖w‖

theorem covarianceFactorMap_apply_local {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (h : Fin n → E) (ξ : Fin n → ℝ) :
    covarianceFactorMap h ξ = ∑ i, ξ i • h i := by
  simp [covarianceFactorMap, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

private lemma covarianceFactorMap_single_local {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (h : Fin n → E) (i : Fin n) :
    covarianceFactorMap h (Pi.single i (1 : ℝ)) = h i := by
  rw [covarianceFactorMap_apply_local]
  simp [Pi.single_apply]

private lemma coordinateDerivative_affine_covarianceFactor {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {G : E → ℝ}
    (hG : ContDiff ℝ 1 G) (A : (Fin n → ℝ) →L[ℝ] E) (x : E)
    (i : Fin n) (ξ : Fin n → ℝ) :
    coordinateDerivative (fun y => G (x + A y)) i ξ =
      fderiv ℝ G (x + A ξ) (A (Pi.single i (1 : ℝ))) := by
  have houter := (hG.differentiable_one (x + A ξ)).hasFDerivAt
  have hinner : HasFDerivAt (fun y : Fin n → ℝ => x + A y) A ξ :=
    A.hasFDerivAt.const_add x
  have hcomp := houter.comp ξ hinner
  have hderiv := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ =>
    L (Pi.single i (1 : ℝ))) hcomp.fderiv
  simpa [Function.comp_def, coordinateDerivative, ContinuousLinearMap.comp_apply] using hderiv

private lemma coordinateDerivative_covarianceFactorObservable {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (x : E) (h : Fin n → E) (i : Fin n) (ξ : Fin n → ℝ) :
    coordinateDerivative (covarianceFactorObservable Φ x h) i ξ =
      fderiv ℝ Φ (x + covarianceFactorMap h ξ) (h i) := by
  let A : (Fin n → ℝ) →L[ℝ] E := covarianceFactorMap h
  calc
    coordinateDerivative (covarianceFactorObservable Φ x h) i ξ =
        fderiv ℝ Φ (x + A ξ) (A (Pi.single i (1 : ℝ))) :=
      coordinateDerivative_affine_covarianceFactor hΦ A x i ξ
    _ = fderiv ℝ Φ (x + covarianceFactorMap h ξ) (h i) := by
      rw [show A (Pi.single i (1 : ℝ)) = h i from covarianceFactorMap_single_local h i]

private lemma secondCoordinate_covarianceFactorObservable {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → ℝ}
    (hΦ : ContDiff ℝ 2 Φ) (x : E) (h : Fin n → E)
    (i j : Fin n) (ξ : Fin n → ℝ) :
    coordinateDerivative (coordinateDerivative (covarianceFactorObservable Φ x h) i) j ξ =
      fderiv ℝ (fun z => fderiv ℝ Φ z (h i))
        (x + covarianceFactorMap h ξ) (h j) := by
  let A : (Fin n → ℝ) →L[ℝ] E := covarianceFactorMap h
  let G : E → ℝ := fun y => fderiv ℝ Φ y (h i)
  have hG : ContDiff ℝ 1 G := by
    have hregularity := hΦ.contDiff_fderiv_apply (m := 1)
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    have hpair : ContDiff ℝ 1 (fun y : E => (y, h i)) :=
      contDiff_id.prodMk contDiff_const
    simpa [G, Function.comp_def] using hregularity.comp hpair
  have hpartial : coordinateDerivative (covarianceFactorObservable Φ x h) i =
      fun η => G (x + A η) := by
    funext η
    exact coordinateDerivative_covarianceFactorObservable
      (hΦ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) x h i η
  rw [hpartial]
  change coordinateDerivative (fun η => G (x + A η)) j ξ = _
  rw [coordinateDerivative_affine_covarianceFactor hG A x j ξ]
  rw [show A (Pi.single j (1 : ℝ)) = h j from covarianceFactorMap_single_local h j]

private lemma covarianceFactorMap_norm_le {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (h : Fin n → E) (ξ : Fin n → ℝ) :
    ‖covarianceFactorMap h ξ‖ ≤ (∑ i, ‖h i‖) * ‖ξ‖ := by
  rw [covarianceFactorMap_apply_local]
  calc
    ‖∑ i, ξ i • h i‖ ≤ ∑ i, ‖ξ i • h i‖ := norm_sum_le _ _
    _ = ∑ i, ‖ξ i‖ * ‖h i‖ := by simp [norm_smul]
    _ ≤ ∑ i, ‖ξ‖ * ‖h i‖ := by
      gcongr
      exact norm_le_pi_norm ξ i
    _ = (∑ i, ‖h i‖) * ‖ξ‖ := by
      calc
        _ = ∑ i, ‖h i‖ * ‖ξ‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by rw [← Finset.sum_mul]

/-- The finite-dimensional affine pullback inherits the polynomial derivative bounds needed by
the finite heat theorem from the Fréchet derivative bounds on `Φ`. -/
theorem hasPolynomiallyBoundedSecondCoordinateDerivatives_covarianceFactorObservable
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → ℝ} (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (x : E)
    (h : Fin n → E) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives
      (covarianceFactorObservable Φ x h) := by
  rcases hΦ with ⟨hC2, C, hC, d, hvalue, hfirst, hsecond⟩
  let B : ℝ := 1 + ‖x‖ + ∑ i, ‖h i‖
  let D : ℝ := 1 + ∑ i, ‖h i‖ ^ 2
  let C' : ℝ := C * B ^ d * D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  have hBump (ξ : Fin n → ℝ) :
      1 + ‖x + covarianceFactorMap h ξ‖ ≤ B * (1 + ‖ξ‖) := by
    have hA := covarianceFactorMap_norm_le h ξ
    have hs : 0 ≤ ∑ i, ‖h i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hξ : 0 ≤ ‖ξ‖ := norm_nonneg _
    have hx : 0 ≤ ‖x‖ := norm_nonneg _
    dsimp [B]
    calc
      1 + ‖x + covarianceFactorMap h ξ‖ ≤
          1 + ‖x‖ + ‖covarianceFactorMap h ξ‖ := by
            linarith [norm_add_le x (covarianceFactorMap h ξ)]
      _ ≤ 1 + ‖x‖ + (∑ i, ‖h i‖) * ‖ξ‖ := by linarith
      _ ≤ (1 + ‖x‖ + ∑ i, ‖h i‖) * (1 + ‖ξ‖) := by
        nlinarith [mul_nonneg (by positivity : 0 ≤ 1 + ‖x‖) hξ]
  have hDir2 (i : Fin n) : ‖h i‖ ^ 2 ≤ D := by
    dsimp [D]
    have hterm := Finset.single_le_sum (s := Finset.univ) (f := fun j => ‖h j‖ ^ 2)
      (fun j _ => sq_nonneg ‖h j‖) (Finset.mem_univ i)
    nlinarith
  have hDirProd (i j : Fin n) : ‖h i‖ * ‖h j‖ ≤ D := by
    have hi := hDir2 i
    have hj := hDir2 j
    have hsum := sq_nonneg (‖h i‖ - ‖h j‖)
    nlinarith
  have hDge : 1 ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hC1 : ContDiff ℝ 1 Φ := hC2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hAcont : ContDiff ℝ 2 (fun ξ : Fin n → ℝ => x + covarianceFactorMap h ξ) := by
    exact contDiff_const.add (covarianceFactorMap h).contDiff
  refine ⟨hC2.comp hAcont, C', hC', d, ?_, ?_, ?_⟩
  · intro ξ
    change |Φ (x + covarianceFactorMap h ξ)| ≤ _
    calc
      |Φ (x + covarianceFactorMap h ξ)| ≤
          C * (1 + ‖x + covarianceFactorMap h ξ‖) ^ d := hvalue _
      _ ≤ C * (B * (1 + ‖ξ‖)) ^ d := by
        gcongr
        exact hBump ξ
      _ = C * B ^ d * (1 + ‖ξ‖) ^ d := by rw [mul_pow]; ring
      _ ≤ C' * (1 + ‖ξ‖) ^ d := by
        dsimp [C']
        have hz : 0 ≤ C * B ^ d * (1 + ‖ξ‖) ^ d := by positivity
        have := mul_le_mul_of_nonneg_left hDge hz
        nlinarith
  · intro i ξ
    rw [coordinateDerivative_covarianceFactorObservable hC1 x h i ξ]
    have hi : ‖h i‖ ≤ D := by
      have hi2 := hDir2 i
      have hnonneg := norm_nonneg (h i)
      dsimp [D] at hi2 ⊢
      nlinarith
    calc
      |fderiv ℝ Φ (x + covarianceFactorMap h ξ) (h i)| ≤
          ‖fderiv ℝ Φ (x + covarianceFactorMap h ξ)‖ * ‖h i‖ := by
            rw [← Real.norm_eq_abs]
            exact (fderiv ℝ Φ (x + covarianceFactorMap h ξ)).le_opNorm _
      _ ≤ C * (1 + ‖x + covarianceFactorMap h ξ‖) ^ d * D := by
        exact mul_le_mul (hfirst _) hi (by positivity) (by positivity)
      _ ≤ C * (B * (1 + ‖ξ‖)) ^ d * D := by
        gcongr
        exact hBump ξ
      _ = C' * (1 + ‖ξ‖) ^ d := by
        dsimp [C']
        rw [mul_pow]
        ring
  · intro i j ξ
    rw [secondCoordinate_covarianceFactorObservable hC2 x h i j ξ]
    have hsecond' := hsecond (x + covarianceFactorMap h ξ) (h j) (h i)
    calc
      |fderiv ℝ (fun z => fderiv ℝ Φ z (h i))
          (x + covarianceFactorMap h ξ) (h j)| ≤
          C * (1 + ‖x + covarianceFactorMap h ξ‖) ^ d * ‖h j‖ * ‖h i‖ := by
            exact hsecond'
      _ ≤ C * (1 + ‖x + covarianceFactorMap h ξ‖) ^ d * D := by
        calc
          _ = (C * (1 + ‖x + covarianceFactorMap h ξ‖) ^ d) *
              (‖h j‖ * ‖h i‖) := by ring
          _ ≤ (C * (1 + ‖x + covarianceFactorMap h ξ‖) ^ d) * D :=
            mul_le_mul_of_nonneg_left (hDirProd j i) (by positivity)
          _ = _ := by ring
      _ ≤ C * (B * (1 + ‖ξ‖)) ^ d * D := by
        gcongr
        exact hBump ξ
      _ = C' * (1 + ‖ξ‖) ^ d := by
        dsimp [C']
        rw [mul_pow]
        ring

theorem continuous_secondDirectionalDerivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → ℝ}
    (hΦ : ContDiff ℝ 2 Φ) (w : E) :
    Continuous (fun y => secondDirectionalDerivative Φ y w) := by
  let G : E → ℝ := fun y => fderiv ℝ Φ y w
  have hG : ContDiff ℝ 1 G := by
    have h := hΦ.contDiff_fderiv_apply (m := 1)
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    have hpair : ContDiff ℝ 1 (fun y : E => (y, w)) :=
      contDiff_id.prodMk contDiff_const
    simpa [G, Function.comp_def] using h.comp hpair
  have hF := hG.continuous_fderiv_apply (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hpair : Continuous (fun y : E => (y, w)) := continuous_id.prodMk continuous_const
  change Continuous (fun y => (fderiv ℝ G y) w)
  simpa [secondDirectionalDerivative, G, Function.comp_def] using hF.comp hpair

/-- The finite heat identity transported to the countable product law. -/
theorem hasDerivAt_gaussianPartialSumHeatAverage {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] {v : ℕ → V}
    (T : V →L[ℝ] E) (Φ : E → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ)
    (x : E) {n : ℕ} {t : ℝ} (ht : 0 < t) :
    HasDerivAt (gaussianPartialSumHeatAverage (v := v) T Φ x n)
      ((1 / 2 : ℝ) * ∫ ω, ∑ j ∈ Finset.range n,
        secondDirectionalDerivative Φ
          (x + Real.sqrt t • T (gaussianPartialSum v n ω)) (T (v j))
        ∂standardGaussianInfinitePi) t := by
  let e : (Finset.range n) ≃ Fin n :=
    (Finset.range n).equivFinOfCardEq (by simp)
  let h : Fin n → E := fun i => T (v (e.symm i).1)
  have hgrowth := hasPolynomiallyBoundedSecondCoordinateDerivatives_covarianceFactorObservable
    hΦ x h
  have hcore := hasDerivAt_heatAverage_affineFactor hΦ.1 x h hgrowth ht
  have hvalue (s : ℝ) : gaussianPartialSumHeatAverage (v := v) T Φ x n s =
      heatAverage (covarianceFactorObservable Φ x h) 0 s := by
    unfold gaussianPartialSumHeatAverage
    rw [integral_gaussianPartialSum_eq_integral_standardPi (v := v)
      (f := fun y => Φ (x + Real.sqrt s • T y))]
    · unfold heatAverage shiftAverage covarianceFactorObservable
      apply integral_congr_ae
      filter_upwards [] with ξ
      simp only [zero_add]
      congr 1
      simp [covarianceFactorMap_apply_local, map_sum, h, e, Finset.smul_sum,
        smul_smul, mul_comm]
    · apply hΦ.1.continuous.comp
      exact continuous_const.add
        ((continuous_const : Continuous fun _ : V => Real.sqrt s).smul T.continuous)
  have htrace (s : ℝ) :
      ∫ ξ, ∑ i : Fin n,
        secondDirectionalDerivative Φ
          (x + Real.sqrt s • covarianceFactorMap h ξ) (h i)
        ∂standardGaussianPi n =
      ∫ ω, ∑ j ∈ Finset.range n,
        secondDirectionalDerivative Φ
          (x + Real.sqrt s • T (gaussianPartialSum v n ω)) (T (v j))
        ∂standardGaussianInfinitePi := by
    let f : V → ℝ := fun y => ∑ i : Fin n,
      secondDirectionalDerivative Φ (x + Real.sqrt s • T y) (h i)
    have hf : Continuous f := by
      dsimp [f]
      have hY : Continuous (fun y : V => x + Real.sqrt s • T y) := by
        exact continuous_const.add
          ((continuous_const : Continuous fun _ : V => Real.sqrt s).smul T.continuous)
      apply continuous_finsetSum Finset.univ
      intro i hi
      exact (continuous_secondDirectionalDerivative hΦ.1 (h i)).comp hY
    have hlaw := integral_gaussianPartialSum_eq_integral_standardPi
      (n := n) (v := v) (f := f) hf
    calc
      (∫ ξ, ∑ i : Fin n,
          secondDirectionalDerivative Φ
            (x + Real.sqrt s • covarianceFactorMap h ξ) (h i)
          ∂standardGaussianPi n) =
        ∫ ξ, f (∑ i : Fin n, ξ i • v ((e.symm i).1))
          ∂standardGaussianPi n := by
            apply integral_congr_ae
            filter_upwards [] with ξ
            dsimp [f]
            have harg : x + Real.sqrt s • covarianceFactorMap h ξ =
                x + Real.sqrt s • T (∑ i : Fin n, ξ i • v ((e.symm i).1)) := by
              rw [covarianceFactorMap_apply_local, map_sum]
              simp [h, e, map_smul]
            rw [harg]
      _ = ∫ ω, f (gaussianPartialSum v n ω) ∂standardGaussianInfinitePi := hlaw.symm
      _ = ∫ ω, ∑ j ∈ Finset.range n,
          secondDirectionalDerivative Φ
            (x + Real.sqrt s • T (gaussianPartialSum v n ω)) (T (v j))
          ∂standardGaussianInfinitePi := by
            apply integral_congr_ae
            filter_upwards [] with ω
            dsimp [f]
            let g : ℕ → ℝ := fun j =>
              secondDirectionalDerivative Φ
                (x + Real.sqrt s • T (gaussianPartialSum v n ω)) (T (v j))
            have hsum : ∑ i : Fin n, g (e.symm i).1 =
                ∑ j ∈ Finset.range n, g j := by
              calc
                ∑ i : Fin n, g (e.symm i).1 = ∑ j : Finset.range n, g j.1 :=
                  Equiv.sum_comp e.symm (fun j : Finset.range n => g j.1)
                _ = ∑ j ∈ (Finset.range n).attach, g j.1 := by
                  rw [← Finset.attach_eq_univ]
                _ = ∑ j ∈ Finset.range n, g j := Finset.sum_attach _ _
            simpa [g, h, e] using hsum
  have hderiv := hcore.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => hvalue s)
  convert hderiv using 1
  have htr := htrace t
  simp only [covarianceFactorMap_apply_local] at htr
  rw [← htr]

theorem summable_sq_norm_gaussianDirections {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E) :
    Summable (fun j => ‖T (v j)‖ ^ 2) := by
  have hbound : Summable (fun j => ‖T‖ ^ 2 * ‖v j‖ ^ 2) := hA.mul_left _
  apply hbound.of_nonneg_of_le (fun j => sq_nonneg ‖T (v j)‖)
  intro j
  calc
    ‖T (v j)‖ ^ 2 ≤ (‖T‖ * ‖v j‖) ^ 2 := by
      gcongr
      exact T.le_opNorm (v j)
    _ = ‖T‖ ^ 2 * ‖v j‖ ^ 2 := by rw [mul_pow]

theorem integrable_one_add_norm_pow_of_memLp {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [IsFiniteMeasure standardGaussianInfinitePi]
    {Y : (ℕ → ℝ) → E} {d : ℕ}
    (hY : MemLp Y ((d + 2 : ℕ) : ℝ≥0∞) standardGaussianInfinitePi) :
    Integrable (fun ω => (1 + ‖Y ω‖) ^ d) standardGaussianInfinitePi := by
  have hnorm : MemLp (fun ω => ‖Y ω‖) ((d + 2 : ℕ) : ℝ≥0∞)
      standardGaussianInfinitePi := hY.norm
  have hconst : MemLp (fun _ : ℕ → ℝ => (1 : ℝ)) ((d + 2 : ℕ) : ℝ≥0∞)
      standardGaussianInfinitePi := memLp_const 1
  have hplus : MemLp (fun ω => 1 + ‖Y ω‖) ((d + 2 : ℕ) : ℝ≥0∞)
      standardGaussianInfinitePi := by
    convert hconst.add hnorm using 1
  have hhigh : Integrable (fun ω => ‖1 + ‖Y ω‖‖ ^ (d + 2))
      standardGaussianInfinitePi := hplus.integrable_norm_pow (by omega)
  have hlow := integrable_norm_pow_of_le (f := fun ω => 1 + ‖Y ω‖)
    hplus.aestronglyMeasurable (p := d) (q := d + 2) (by omega) hhigh
  convert hlow using 1
  ext ω
  rw [Real.norm_eq_abs, abs_of_nonneg]
  positivity

/-- The selected limit is bounded almost everywhere by the fast-subsequence envelope. -/
theorem ae_norm_gaussianSeriesLimit_le_fastEnvelope {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) :
    ∀ᵐ ω ∂standardGaussianInfinitePi,
      ‖gaussianSeriesLimit v hA ω‖ ≤ gaussianFastEnvelope hA ω := by
  filter_upwards [ae_tendsto_gaussianSeriesLimit v hA,
    ae_norm_gaussianFastPartialSum_le_envelope hA] with ω hlim hbound
  exact le_of_tendsto' (tendsto_norm.comp hlim) hbound

/-- A fixed finite time interval gives a common polynomial bound for all fast truncations and the
selected limit. -/
theorem ae_gaussianFastArgument_growth_bound {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E) (x : E)
    {M t : ℝ} (htM : t ≤ M) :
    ∀ᵐ ω ∂standardGaussianInfinitePi,
      (∀ k, 1 + ‖x + Real.sqrt t • T (gaussianFastPartialSumSequence hA k ω)‖ ≤
        (1 + ‖x‖ + Real.sqrt M * ‖T‖) * (1 + gaussianFastEnvelope hA ω)) ∧
      1 + ‖gaussianSeriesHeatArgument hA T x t ω‖ ≤
        (1 + ‖x‖ + Real.sqrt M * ‖T‖) * (1 + gaussianFastEnvelope hA ω) := by
  have hsqrtM : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
  have hsqrt : Real.sqrt t ≤ Real.sqrt M := Real.sqrt_le_sqrt htM
  have henv : ∀ ω, 0 ≤ gaussianFastEnvelope hA ω := by
    intro ω
    dsimp [gaussianFastEnvelope, gaussianFastVariation]
    exact add_nonneg (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _)
  filter_upwards [ae_norm_gaussianFastPartialSum_le_envelope hA,
    ae_norm_gaussianSeriesLimit_le_fastEnvelope hA] with ω hpartial hlimit
  constructor
  · intro k
    have hnormT : ‖T (gaussianFastPartialSumSequence hA k ω)‖ ≤
        ‖T‖ * gaussianFastEnvelope hA ω := by
      calc
        ‖T (gaussianFastPartialSumSequence hA k ω)‖ ≤
            ‖T‖ * ‖gaussianFastPartialSumSequence hA k ω‖ := T.le_opNorm _
        _ ≤ _ := mul_le_mul_of_nonneg_left (hpartial k) (norm_nonneg _)
    have harg : ‖x + Real.sqrt t • T (gaussianFastPartialSumSequence hA k ω)‖ ≤
        ‖x‖ + Real.sqrt M * (‖T‖ * gaussianFastEnvelope hA ω) := by
      calc
        _ ≤ ‖x‖ + ‖Real.sqrt t • T (gaussianFastPartialSumSequence hA k ω)‖ := norm_add_le _ _
        _ = ‖x‖ + Real.sqrt t *
            ‖T (gaussianFastPartialSumSequence hA k ω)‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ ‖x‖ + Real.sqrt M * (‖T‖ * gaussianFastEnvelope hA ω) := by
          simpa using add_le_add_left
            (mul_le_mul hsqrt hnormT (norm_nonneg _) hsqrtM) ‖x‖
    have hnonneg : 0 ≤ gaussianFastEnvelope hA ω := henv ω
    calc
      _ ≤ 1 + ‖x‖ + Real.sqrt M * (‖T‖ * gaussianFastEnvelope hA ω) := by linarith
      _ ≤ (1 + ‖x‖ + Real.sqrt M * ‖T‖) * (1 + gaussianFastEnvelope hA ω) := by
        have hprod := mul_nonneg (by positivity : 0 ≤ 1 + ‖x‖) hnonneg
        have hTnonneg : 0 ≤ Real.sqrt M * ‖T‖ := mul_nonneg hsqrtM (norm_nonneg _)
        nlinarith
  · dsimp [gaussianSeriesHeatArgument, gaussianSeriesLimitE]
    have hnormT : ‖T (gaussianSeriesLimit v hA ω)‖ ≤
        ‖T‖ * gaussianFastEnvelope hA ω := by
      calc
        ‖T (gaussianSeriesLimit v hA ω)‖ ≤ ‖T‖ * ‖gaussianSeriesLimit v hA ω‖ := T.le_opNorm _
        _ ≤ _ := mul_le_mul_of_nonneg_left hlimit (norm_nonneg _)
    have harg : ‖x + Real.sqrt t • T (gaussianSeriesLimit v hA ω)‖ ≤
        ‖x‖ + Real.sqrt M * (‖T‖ * gaussianFastEnvelope hA ω) := by
      calc
        _ ≤ ‖x‖ + ‖Real.sqrt t • T (gaussianSeriesLimit v hA ω)‖ := norm_add_le _ _
        _ = ‖x‖ + Real.sqrt t * ‖T (gaussianSeriesLimit v hA ω)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ ‖x‖ + Real.sqrt M * (‖T‖ * gaussianFastEnvelope hA ω) := by
          simpa using add_le_add_left
            (mul_le_mul hsqrt hnormT (norm_nonneg _) hsqrtM) ‖x‖
    have hnonneg : 0 ≤ gaussianFastEnvelope hA ω := henv ω
    calc
      _ ≤ 1 + ‖x‖ + Real.sqrt M * (‖T‖ * gaussianFastEnvelope hA ω) := by linarith
      _ ≤ (1 + ‖x‖ + Real.sqrt M * ‖T‖) * (1 + gaussianFastEnvelope hA ω) := by
        have hprod := mul_nonneg (by positivity : 0 ≤ 1 + ‖x‖) hnonneg
        have hTnonneg : 0 ≤ Real.sqrt M * ‖T‖ := mul_nonneg hsqrtM (norm_nonneg _)
        nlinarith

/-- Every finite polynomial moment of one plus the fast envelope is integrable. -/
theorem integrable_fastEnvelope_polynomial {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (d : ℕ) :
    Integrable (fun ω => (1 + gaussianFastEnvelope hA ω) ^ d) standardGaussianInfinitePi := by
  have hp : 2 ≤ ((d + 2 : ℕ) : ℝ) := by norm_cast; omega
  have hmem := memLp_gaussianFastEnvelope hA (p := ((d + 2 : ℕ) : ℝ)) hp
  have hmem' : MemLp (gaussianFastEnvelope hA) ((d + 2 : ℕ) : ℝ≥0∞)
      standardGaussianInfinitePi := by
    simpa only [ENNReal.ofReal_natCast] using hmem
  have hpoly := integrable_one_add_norm_pow_of_memLp (E := ℝ) (d := d) hmem'
  have hnonneg : ∀ ω, 0 ≤ gaussianFastEnvelope hA ω := by
    intro ω
    dsimp [gaussianFastEnvelope, gaussianFastVariation]
    exact add_nonneg (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _)
  convert hpoly using 1
  ext ω
  rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg ω)]

/-- The heat average of the selected a.e. Gaussian-series version. -/
noncomputable def gaussianSeriesHeatAverage {V E : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] {v : ℕ → V}
    (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E) (Φ : E → ℝ)
    (x : E) (t : ℝ) : ℝ :=
  ∫ ω, Φ (gaussianSeriesHeatArgument hA T x t ω) ∂standardGaussianInfinitePi

/-- The finite heat average taken along the chosen fast subsequence. -/
noncomputable def gaussianFastHeatAverage {V E : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] {v : ℕ → V}
    (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E) (Φ : E → ℝ)
    (x : E) (k : ℕ) (t : ℝ) : ℝ :=
  ∫ ω, Φ (x + Real.sqrt t • T (gaussianFastPartialSumSequence hA k ω))
    ∂standardGaussianInfinitePi

/-- Dominated convergence of the finite heat averages along the fast subsequence. -/
theorem tendsto_gaussianFastHeatAverage {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] {v : ℕ → V}
    (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E) (Φ : E → ℝ)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (x : E) {t : ℝ} :
    Tendsto (fun k => gaussianFastHeatAverage hA T Φ x k t) atTop
      (𝓝 (gaussianSeriesHeatAverage hA T Φ x t)) := by
  rcases hΦ with ⟨hC2, C, hC, d, hvalue, hfirst, hsecond⟩
  let B : ℝ := 1 + ‖x‖ + Real.sqrt t * ‖T‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have harg := ae_gaussianFastArgument_growth_bound hA T x (M := t) (t := t) le_rfl
  let P : (ℕ → ℝ) → ℝ := fun ω => (1 + gaussianFastEnvelope hA ω) ^ d
  let K : ℝ := C * B ^ d
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hbound : ∀ k, ∀ᵐ ω ∂standardGaussianInfinitePi,
      ‖Φ (x + Real.sqrt t • T (gaussianFastPartialSumSequence hA k ω))‖ ≤
        P ω * K := by
    intro k
    filter_upwards [harg] with ω hω
    rw [Real.norm_eq_abs]
    calc
      |Φ (x + Real.sqrt t • T (gaussianFastPartialSumSequence hA k ω))|
          ≤ C * (1 + ‖x + Real.sqrt t • T (gaussianFastPartialSumSequence hA k ω)‖) ^ d :=
            hvalue _
      _ ≤ C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d := by
        gcongr
        exact hω.1 k
      _ = P ω * K := by dsimp [P, K, B]; rw [mul_pow]; ring
  have hboundLimit : ∀ᵐ ω ∂standardGaussianInfinitePi,
      ‖Φ (gaussianSeriesHeatArgument hA T x t ω)‖ ≤ P ω * K := by
    filter_upwards [harg] with ω hω
    rw [Real.norm_eq_abs]
    calc
      |Φ (gaussianSeriesHeatArgument hA T x t ω)| ≤
          C * (1 + ‖gaussianSeriesHeatArgument hA T x t ω‖) ^ d := hvalue _
      _ ≤ C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d := by
        gcongr
        exact hω.2
      _ = P ω * K := by dsimp [P, K, B]; rw [mul_pow]; ring
  have hdomInt : Integrable (fun ω => P ω * K) standardGaussianInfinitePi := by
    simpa [P] using (integrable_fastEnvelope_polynomial hA d).mul_const K
  have hFmeas (k : ℕ) : AEStronglyMeasurable
      (fun ω => Φ (x + Real.sqrt t • T (gaussianFastPartialSumSequence hA k ω)))
      standardGaussianInfinitePi := by
    let hm := memLp_gaussianPartialSum v (p := 2) (by norm_num) hA
      (gaussianFastIndex hA k)
    let G : V → ℝ := fun z => Φ (x + Real.sqrt t • T z)
    have hG : Continuous G := by
      dsimp [G]
      exact hC2.continuous.comp (continuous_const.add
        ((continuous_const : Continuous fun _ : V => Real.sqrt t).smul T.continuous))
    exact hG.comp_aestronglyMeasurable hm.aestronglyMeasurable
  have hG : Continuous (fun z : V => Φ (x + Real.sqrt t • T z)) := by
    exact hC2.continuous.comp (continuous_const.add
      ((continuous_const : Continuous fun _ : V => Real.sqrt t).smul T.continuous))
  have hlimmeas : AEStronglyMeasurable
      (fun ω => Φ (gaussianSeriesHeatArgument hA T x t ω)) standardGaussianInfinitePi := by
    exact (hG.comp_stronglyMeasurable (stronglyMeasurable_gaussianSeriesLimit v hA)).aestronglyMeasurable
  have hlim : ∀ᵐ ω ∂standardGaussianInfinitePi, Tendsto
      (fun k => Φ (x + Real.sqrt t • T (gaussianFastPartialSumSequence hA k ω))) atTop
      (𝓝 (Φ (gaussianSeriesHeatArgument hA T x t ω))) := by
    filter_upwards [ae_tendsto_gaussianSeriesLimit v hA] with ω hω
    have hcomp := hG.continuousAt.tendsto.comp hω
    change Tendsto (fun k => (fun z : V => Φ (x + Real.sqrt t • T z))
      (gaussianFastPartialSumSequence hA k ω)) atTop _
    exact hcomp
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (fun ω => P ω * K) (Filter.Eventually.of_forall hFmeas) (Filter.Eventually.of_forall hbound)
    hdomInt hlim
  simpa [gaussianFastHeatAverage, gaussianSeriesHeatAverage, P] using hconv

/-- The derivative growth clause in `HasPolynomiallyBoundedC2Derivatives` yields the directional
Hessian bound used to sum the infinite trace. -/
theorem hasPolynomiallyBoundedSecondDirectionalDerivative_of_C2Derivatives
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → ℝ}
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) :
    HasPolynomiallyBoundedSecondDirectionalDerivative Φ := by
  rcases hΦ with ⟨_, C, hC, d, _, _, hsecond⟩
  refine ⟨C, hC, d, ?_⟩
  intro y w
  calc
    |secondDirectionalDerivative Φ y w| ≤
        C * (1 + ‖y‖) ^ d * ‖w‖ * ‖w‖ := by
          change |fderiv ℝ (fun z => fderiv ℝ Φ z w) y w| ≤ _
          exact hsecond y w w
    _ = C * (1 + ‖y‖) ^ d * ‖w‖ ^ 2 := by ring

/-- The infinite Hessian trace at time `t`, as a pointwise sum over the mapped directions. -/
noncomputable def gaussianSeriesHeatTrace {V E : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (x : E) (t : ℝ) (ω : ℕ → ℝ) : ℝ :=
  ∑' j, secondDirectionalDerivative Φ
    (gaussianSeriesHeatArgument hA T x t ω) (T (v j))

/-- The finite Hessian trace in the heat identity along the fast subsequence. -/
noncomputable def gaussianFastHeatTrace {V E : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (x : E) (k : ℕ) (t : ℝ) (ω : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (gaussianFastIndex hA k),
    secondDirectionalDerivative Φ
      (x + Real.sqrt t • T (gaussianFastPartialSumSequence hA k ω)) (T (v j))

/-- The expected infinite Hessian trace in the heat identity. -/
noncomputable def gaussianSeriesHeatTraceAverage {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] {v : ℕ → V}
    (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E) (Φ : E → ℝ)
    (x : E) (t : ℝ) : ℝ :=
  ∫ ω, gaussianSeriesHeatTrace hA T Φ x t ω ∂standardGaussianInfinitePi

/-- The expected finite Hessian trace along the chosen fast subsequence. -/
noncomputable def gaussianFastHeatTraceAverage {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] {v : ℕ → V}
    (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E) (Φ : E → ℝ)
    (x : E) (k : ℕ) (t : ℝ) : ℝ :=
  ∫ ω, gaussianFastHeatTrace hA T Φ x k t ω ∂standardGaussianInfinitePi

/-- The finite-rank heat identity for the selected fast truncations. -/
theorem hasDerivAt_gaussianFastHeatAverage {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] {v : ℕ → V}
    (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E) (Φ : E → ℝ)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (x : E) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    HasDerivAt (gaussianFastHeatAverage hA T Φ x k)
      ((1 / 2 : ℝ) * gaussianFastHeatTraceAverage hA T Φ x k t) t := by
  have hfinite := hasDerivAt_gaussianPartialSumHeatAverage (v := v) T Φ hΦ x
    (n := gaussianFastIndex hA k) ht
  have heq : gaussianFastHeatAverage hA T Φ x k =
      gaussianPartialSumHeatAverage (v := v) T Φ x (gaussianFastIndex hA k) := by
    funext s
    rfl
  rw [heq]
  simpa [gaussianFastHeatTraceAverage, gaussianFastHeatTrace,
    gaussianFastPartialSumSequence] using hfinite

/-- The finite Hessian traces converge pointwise almost everywhere to the infinite trace. -/
theorem ae_tendsto_gaussianFastHeatTrace {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (hΦ : ContDiff ℝ 2 Φ)
    (hGrowth : HasPolynomiallyBoundedSecondDirectionalDerivative Φ)
    (x : E) (t : ℝ) :
    ∀ᵐ ω ∂standardGaussianInfinitePi,
      Tendsto (fun k => gaussianFastHeatTrace hA T Φ x k t ω) atTop
        (𝓝 (gaussianSeriesHeatTrace hA T Φ x t ω)) := by
  rcases hGrowth with ⟨C, hC, d, hsecond⟩
  let B : ℝ := 1 + ‖x‖ + Real.sqrt t * ‖T‖
  let H : ℕ → E := fun j => T (v j)
  let F : ℕ → (ℕ → ℝ) → V := gaussianFastPartialSumSequence hA
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hdir := summable_sq_norm_gaussianDirections hA T
  have hindex : Tendsto (gaussianFastIndex hA) atTop atTop :=
    (gaussianFastIndex_strictMono hA).tendsto_atTop
  have harg := ae_gaussianFastArgument_growth_bound hA T x (M := t) (t := t) le_rfl
  filter_upwards [ae_tendsto_gaussianSeriesLimit v hA, harg] with ω hseq hbound
  let u : ℕ → ℝ := fun j => C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d * ‖H j‖ ^ 2
  have hu : Summable u := by
    simpa [u, H] using hdir.mul_left (C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d)
  let f : ℕ → ℕ → ℝ := fun k j =>
    if j < gaussianFastIndex hA k then
      secondDirectionalDerivative Φ
        (x + Real.sqrt t • T (F k ω)) (H j) else 0
  have hpointBound (k j : ℕ) : ‖f k j‖ ≤ u j := by
    by_cases hj : j < gaussianFastIndex hA k
    · simp [f, hj, u, H]
      calc
        |secondDirectionalDerivative Φ (x + Real.sqrt t • T (F k ω)) (T (v j))|
            ≤ C * (1 + ‖x + Real.sqrt t • T (F k ω)‖) ^ d * ‖T (v j)‖ ^ 2 :=
              hsecond _ _
        _ ≤ C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d * ‖T (v j)‖ ^ 2 := by
          gcongr
          exact hbound.1 k
    · simp [f, hj, u]
      have henv : 0 ≤ gaussianFastEnvelope hA ω := by
        dsimp [gaussianFastEnvelope, gaussianFastVariation]
        exact add_nonneg (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _)
      have hcoef : 0 ≤ C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d := by positivity
      exact mul_nonneg hcoef (sq_nonneg _)
  have htermLimit (j : ℕ) : Tendsto (fun k => f k j) atTop
      (𝓝 (secondDirectionalDerivative Φ
        (gaussianSeriesHeatArgument hA T x t ω) (H j))) := by
    have hcont : Continuous (fun z : V => secondDirectionalDerivative Φ
        (x + Real.sqrt t • T z) (H j)) := by
      exact (continuous_secondDirectionalDerivative hΦ (H j)).comp
          (continuous_const.add
            ((continuous_const : Continuous fun _ : V => Real.sqrt t).smul T.continuous))
    have hraw := hcont.continuousAt.tendsto.comp hseq
    have hidx : ∀ᶠ k in atTop, j < gaussianFastIndex hA k := by
      have hlarge := hindex.eventually (Ici_mem_atTop (j + 1))
      filter_upwards [hlarge] with k hk
      exact Nat.lt_of_lt_of_le (by omega) hk
    have heq : (fun k => f k j) =ᶠ[atTop] fun k =>
        secondDirectionalDerivative Φ (x + Real.sqrt t • T (F k ω)) (H j) := by
      filter_upwards [hidx] with k hk
      simp [f, hk]
    apply hraw.congr'
    filter_upwards [heq] with k hk
    exact hk.symm
  have hsum := tendsto_tsum_of_dominated_convergence hu htermLimit
    (Filter.Eventually.of_forall fun k j => hpointBound k j)
  have hfinite (k : ℕ) : gaussianFastHeatTrace hA T Φ x k t ω = ∑' j, f k j := by
    rw [gaussianFastHeatTrace]
    symm
    rw [tsum_eq_sum (s := Finset.range (gaussianFastIndex hA k))]
    · apply Finset.sum_congr rfl
      intro j hj
      simp [f, H, F, gaussianFastPartialSumSequence, Finset.mem_range.mp hj]
    · intro j hj
      simp [f, Finset.mem_range] at hj ⊢
      omega
  exact hsum.congr (fun k => (hfinite k).symm)

/-- Absolute summability of the Hessian trace holds pointwise, with the expected trace-class
majorant. -/
theorem summable_gaussianSeriesHeatTrace {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (hGrowth : HasPolynomiallyBoundedSecondDirectionalDerivative Φ)
    (x : E) (t : ℝ) (ω : ℕ → ℝ) :
    Summable (fun j => secondDirectionalDerivative Φ
      (gaussianSeriesHeatArgument hA T x t ω) (T (v j))) := by
  rcases hGrowth with ⟨C, hC, d, hsecond⟩
  have hdir := summable_sq_norm_gaussianDirections hA T
  let K : ℝ := C * (1 + ‖gaussianSeriesHeatArgument hA T x t ω‖) ^ d
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hdirK : Summable (fun j => K * ‖T (v j)‖ ^ 2) := hdir.mul_left K
  apply hdirK.of_norm_bounded (fun j => ?_)
  rw [Real.norm_eq_abs]
  calc
    |secondDirectionalDerivative Φ (gaussianSeriesHeatArgument hA T x t ω) (T (v j))|
        ≤ C * (1 + ‖gaussianSeriesHeatArgument hA T x t ω‖) ^ d * ‖T (v j)‖ ^ 2 :=
          hsecond _ _
    _ = K * ‖T (v j)‖ ^ 2 := rfl

/-- The pointwise series is measurable as a.e. limit of its finite traces. -/
theorem aestronglyMeasurable_gaussianSeriesHeatTrace {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] {v : ℕ → V}
    (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E) (Φ : E → ℝ)
    (hΦ : ContDiff ℝ 2 Φ)
    (hGrowth : HasPolynomiallyBoundedSecondDirectionalDerivative Φ) (x : E) (t : ℝ) :
    AEStronglyMeasurable (gaussianSeriesHeatTrace hA T Φ x t) standardGaussianInfinitePi := by
  have hY : StronglyMeasurable (gaussianSeriesHeatArgument hA T x t) := by
    change StronglyMeasurable (fun ω => x + Real.sqrt t • gaussianSeriesLimitE hA T ω)
    have hΨE := stronglyMeasurable_gaussianSeriesLimitE hA T
    have hAffine : Continuous (fun z : E => x + Real.sqrt t • z) := by
      exact continuous_const.add (continuous_id.const_smul (Real.sqrt t))
    exact hAffine.comp_stronglyMeasurable hΨE
  have hpartial (n : ℕ) : StronglyMeasurable (fun ω =>
      ∑ j ∈ Finset.range n,
        secondDirectionalDerivative Φ (gaussianSeriesHeatArgument hA T x t ω) (T (v j))) := by
    let G : E → ℝ := fun y => ∑ j ∈ Finset.range n,
      secondDirectionalDerivative Φ y (T (v j))
    have hG : Continuous G := by
      apply continuous_finsetSum (s := Finset.range n)
      intro j hj
      exact continuous_secondDirectionalDerivative hΦ (T (v j))
    exact hG.comp_stronglyMeasurable hY
  have hpartial' (n : ℕ) : AEStronglyMeasurable
      (fun ω => ∑ j ∈ Finset.range n,
        secondDirectionalDerivative Φ (gaussianSeriesHeatArgument hA T x t ω) (T (v j)))
      standardGaussianInfinitePi := (hpartial n).aestronglyMeasurable
  refine aestronglyMeasurable_of_tendsto_ae atTop hpartial' ?_
  filter_upwards [] with ω
  have hsum := summable_gaussianSeriesHeatTrace hA T Φ hGrowth x t ω
  simpa [gaussianSeriesHeatTrace] using hsum.hasSum.tendsto_sum_nat

/-- The expected finite Hessian traces converge to the expected infinite trace. -/
theorem tendsto_gaussianFastHeatTraceAverage {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace E] {v : ℕ → V}
    (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E) (Φ : E → ℝ)
    (hΦ : ContDiff ℝ 2 Φ)
    (hGrowth : HasPolynomiallyBoundedSecondDirectionalDerivative Φ)
    (x : E) (t : ℝ) :
    Tendsto (fun k => gaussianFastHeatTraceAverage hA T Φ x k t) atTop
      (𝓝 (gaussianSeriesHeatTraceAverage hA T Φ x t)) := by
  rcases hGrowth with ⟨C, hC, d, hsecond⟩
  let B : ℝ := 1 + ‖x‖ + Real.sqrt t * ‖T‖
  let P : (ℕ → ℝ) → ℝ := fun ω => (1 + gaussianFastEnvelope hA ω) ^ d
  let S : ℝ := ∑' j, ‖T (v j)‖ ^ 2
  let K : ℝ := C * B ^ d * S
  have hdir := summable_sq_norm_gaussianDirections hA T
  have harg := ae_gaussianFastArgument_growth_bound hA T x (M := t) (t := t) le_rfl
  have hdomInt : Integrable (fun ω => P ω * K) standardGaussianInfinitePi := by
    simpa [P] using (integrable_fastEnvelope_polynomial hA d).mul_const K
  have hfastMeas (k : ℕ) : AEStronglyMeasurable
      (gaussianFastHeatTrace hA T Φ x k t) standardGaussianInfinitePi := by
    let n := gaussianFastIndex hA k
    let G : V → ℝ := fun z => ∑ j ∈ Finset.range n,
      secondDirectionalDerivative Φ (x + Real.sqrt t • T z) (T (v j))
    have hG : Continuous G := by
      apply continuous_finsetSum (s := Finset.range n)
      intro j hj
      exact (continuous_secondDirectionalDerivative hΦ (T (v j))).comp
        (continuous_const.add
          ((continuous_const : Continuous fun _ : V => Real.sqrt t).smul T.continuous))
    have hm := memLp_gaussianPartialSum v (p := 2) (by norm_num) hA n
    change AEStronglyMeasurable (G ∘ fun ω => gaussianPartialSum v n ω)
      standardGaussianInfinitePi
    exact hG.comp_aestronglyMeasurable hm.aestronglyMeasurable
  have hfastBound (k : ℕ) : ∀ᵐ ω ∂standardGaussianInfinitePi,
      ‖gaussianFastHeatTrace hA T Φ x k t ω‖ ≤ P ω * K := by
    filter_upwards [harg] with ω hω
    let n := gaussianFastIndex hA k
    calc
      ‖gaussianFastHeatTrace hA T Φ x k t ω‖ ≤
          ∑ j ∈ Finset.range n, |secondDirectionalDerivative Φ
            (x + Real.sqrt t • T (gaussianFastPartialSumSequence hA k ω)) (T (v j))| := by
              rw [gaussianFastHeatTrace]
              exact norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range n,
          C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d * ‖T (v j)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          |secondDirectionalDerivative Φ
              (x + Real.sqrt t • T (gaussianFastPartialSumSequence hA k ω)) (T (v j))|
              ≤ C * (1 + ‖x + Real.sqrt t • T (gaussianFastPartialSumSequence hA k ω)‖) ^ d *
                ‖T (v j)‖ ^ 2 := hsecond _ _
          _ ≤ C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d * ‖T (v j)‖ ^ 2 := by
            gcongr
            exact hω.1 k
      _ ≤ ∑' j, C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d * ‖T (v j)‖ ^ 2 := by
        let cω : ℝ := C * (B * (1 + gaussianFastEnvelope hA ω)) ^ d
        have hdirω : Summable (fun j => cω * ‖T (v j)‖ ^ 2) := hdir.mul_left cω
        have henv : 0 ≤ gaussianFastEnvelope hA ω := by
          dsimp [gaussianFastEnvelope, gaussianFastVariation]
          exact add_nonneg (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _)
        have hcω : 0 ≤ cω := by dsimp [cω]; positivity
        simpa [cω] using hdirω.sum_le_tsum (Finset.range n)
          (fun j hj => by exact mul_nonneg hcω (sq_nonneg _))
      _ = P ω * K := by
        rw [hdir.tsum_mul_left]
        dsimp [P, K, S, B]
        rw [mul_pow]
        ring
  have hlim := ae_tendsto_gaussianFastHeatTrace hA T Φ hΦ
    (⟨C, hC, d, hsecond⟩ : HasPolynomiallyBoundedSecondDirectionalDerivative Φ) x t
  have hconv := tendsto_integral_filter_of_dominated_convergence (fun ω => P ω * K)
    (Filter.Eventually.of_forall hfastMeas) (Filter.Eventually.of_forall hfastBound)
    hdomInt hlim
  simpa [gaussianFastHeatTraceAverage, gaussianSeriesHeatTraceAverage] using hconv

end ASDExplicitGamma.Gaussian
