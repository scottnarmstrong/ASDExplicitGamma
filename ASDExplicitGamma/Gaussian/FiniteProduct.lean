/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.Finite
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Product Gaussian integration by parts

Coordinatewise integration by parts for independent standard Gaussian coordinates.
-/

@[expose] public section

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal NNReal

namespace ASDExplicitGamma.Gaussian

/-- The partial derivative in coordinate `i`, expressed as a Fréchet derivative. -/
noncomputable def coordinateDerivative {n : ℕ} (F : (Fin n → ℝ) → ℝ) (i : Fin n)
    (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ F x (Pi.single i 1)

/-- The product law of `n` independent standard real Gaussian coordinates. -/
noncomputable def standardGaussianPi (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)

/-- A `C¹` function and all its coordinate derivatives have a common polynomial bound. -/
def HasPolynomiallyBoundedCoordinateDerivatives {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) : Prop :=
  ContDiff ℝ 1 F ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ,
    (∀ x, |F x| ≤ C * (1 + ‖x‖) ^ d) ∧
    ∀ i x, |F x| + |coordinateDerivative F i x| ≤ C * (1 + ‖x‖) ^ d

/-- The update of a vector in one coordinate has norm controlled by the old vector and the
replacement value. -/
private lemma norm_update_le {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    ‖Function.update x i t‖ ≤ ‖x‖ + |t| := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg _) (abs_nonneg _))).2
  intro j
  rw [Function.update_apply]
  split_ifs with h
  · subst j
    exact le_add_of_nonneg_left (norm_nonneg _)
  · exact (norm_le_pi_norm x j).trans (le_add_of_nonneg_right (abs_nonneg _))

/-- The derivative of a coordinate slice is the corresponding partial derivative. -/
private lemma deriv_update_comp_eq_partial {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : ContDiff ℝ 1 F) (x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    deriv (fun s => F (Function.update x i s)) t =
      coordinateDerivative F i (Function.update x i t) := by
  have hcomp := (hF.differentiable_one (Function.update x i t)).hasFDerivAt.comp t
    (hasDerivAt_update x i t).hasFDerivAt
  have hderiv := hcomp.hasDerivAt.deriv
  simpa [Function.comp_def, coordinateDerivative, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply] using hderiv

/-- The exponential of the sum of absolute coordinates is integrable under a product Gaussian. -/
private lemma integrable_exp_sum_abs_standardGaussianPi (n : ℕ) (a : ℝ) :
    Integrable (fun x : Fin n → ℝ => Real.exp (a * ∑ i, |x i|))
      (standardGaussianPi n) := by
  have hprod : Integrable (fun x : Fin n → ℝ => ∏ i, Real.exp (a * |x i|))
      (standardGaussianPi n) := by
    exact Integrable.fintype_prod (fun _ => integrable_exp_abs_gaussianReal a)
  convert hprod using 1
  ext x
  rw [← Real.exp_sum]
  congr 1
  exact Finset.mul_sum ..

/-- A polynomially bounded measurable function is integrable under a finite product of standard
Gaussian measures. -/
lemma integrable_of_pi_polynomial_bound {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C) {d : ℕ}
    (hg : ∀ x, |f x| ≤ C * (1 + ‖x‖) ^ d) :
    Integrable f (standardGaussianPi n) := by
  have hsum_nonneg (x : Fin n → ℝ) : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hnorm_le_sum (x : Fin n → ℝ) : ‖x‖ ≤ ∑ i, |x i| := by
    apply (pi_norm_le_iff_of_nonneg (hsum_nonneg x)).2
    intro i
    exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
  have hmajor : Integrable
      (fun x : Fin n → ℝ => C * Real.exp ((d : ℝ) * ∑ i, |x i|))
      (standardGaussianPi n) := by
    simpa only [smul_eq_mul] using
      (integrable_exp_sum_abs_standardGaussianPi n (d : ℝ)).const_mul C
  refine Integrable.mono' hmajor hf.aestronglyMeasurable ?_
  filter_upwards with x
  calc
    |f x| ≤ C * (1 + ‖x‖) ^ d := hg x
    _ ≤ C * Real.exp ((d : ℝ) * ∑ i, |x i|) := by
      apply mul_le_mul_of_nonneg_left _ hC
      calc
        (1 + ‖x‖) ^ d ≤ (1 + ∑ i, |x i|) ^ d := by
          gcongr
          exact hnorm_le_sum x
        _ ≤ (Real.exp (∑ i, |x i|)) ^ d := by
          gcongr
          simpa [add_comm] using Real.add_one_le_exp (∑ i, |x i|)
        _ = Real.exp ((d : ℝ) * ∑ i, |x i|) := by rw [← Real.exp_nat_mul]

/-- Multivariate integration by parts for a product of standard Gaussians. -/
theorem integral_eval_mul_eq_integral_coordinateDerivative {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : HasPolynomiallyBoundedCoordinateDerivatives F)
    (i : Fin n) :
    ∫ x, x i * F x ∂(standardGaussianPi n) =
      ∫ x, coordinateDerivative F i x ∂(standardGaussianPi n) := by
  rcases hF.2 with ⟨C, hC, d, hfunctionbound, hbound⟩
  have hFbound : ∀ x, |F x| ≤ C * (1 + ‖x‖) ^ d := by
    exact hfunctionbound
  have hpartialBound : ∀ x, |coordinateDerivative F i x| ≤ C * (1 + ‖x‖) ^ d := by
    intro x
    calc
      |coordinateDerivative F i x| ≤ |F x| + |coordinateDerivative F i x| :=
        le_add_of_nonneg_left (abs_nonneg _)
      _ ≤ C * (1 + ‖x‖) ^ d := hbound i x
  have hmulBound : ∀ x, |x i * F x| ≤ C * (1 + ‖x‖) ^ (d + 1) := by
    intro x
    calc
      |x i * F x| = |x i| * |F x| := abs_mul _ _
      _ ≤ (1 + ‖x‖) * (C * (1 + ‖x‖) ^ d) := by
        have hxi : |x i| ≤ 1 + ‖x‖ := by
          exact (norm_le_pi_norm x i).trans (by linarith [norm_nonneg x])
        exact mul_le_mul hxi (hFbound x) (by positivity) (by positivity)
      _ = C * (1 + ‖x‖) ^ (d + 1) := by rw [pow_succ]; ring
  have hFmeas : Measurable F := hF.1.continuous.measurable
  have hpartialMeas : Measurable (coordinateDerivative F i) := by
    unfold coordinateDerivative
    exact (hF.1.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.measurable
  have hmulMeas : Measurable (fun x => x i * F x) := (measurable_pi_apply i).mul hFmeas
  have hFint : Integrable F (standardGaussianPi n) :=
    integrable_of_pi_polynomial_bound hFmeas hC hFbound
  have hpartialInt : Integrable (coordinateDerivative F i) (standardGaussianPi n) :=
    integrable_of_pi_polynomial_bound hpartialMeas hC hpartialBound
  have hmulInt : Integrable (fun x => x i * F x) (standardGaussianPi n) :=
    integrable_of_pi_polynomial_bound hmulMeas hC hmulBound
  cases n with
  | zero => exact Fin.elim0 i
  | succ k =>
    let μ : ∀ j : Fin (k + 1), Measure ℝ := fun _ => gaussianReal 0 1
    let ν : Measure (Fin k → ℝ) := Measure.pi (fun _ : Fin k => gaussianReal 0 1)
    let e : (Fin (k + 1) → ℝ) ≃ᵐ ℝ × (Fin k → ℝ) :=
      MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i
    have hem : MeasurePreserving e (standardGaussianPi (k + 1))
        ((gaussianReal 0 1).prod ν) := by
      dsimp only [e, standardGaussianPi, ν, μ]
      exact measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => gaussianReal 0 1) i
    let lhsProd : ℝ × (Fin k → ℝ) → ℝ := fun z => z.1 * F (e.symm z)
    let rhsProd : ℝ × (Fin k → ℝ) → ℝ := fun z => coordinateDerivative F i (e.symm z)
    have lhsProdInt : Integrable lhsProd ((gaussianReal 0 1).prod ν) := by
      have h := hem.symm.integrable_comp_of_integrable hmulInt
      simpa [lhsProd, Function.comp_def, e, MeasurableEquiv.piFinSuccAbove_symm_apply] using h
    have rhsProdInt : Integrable rhsProd ((gaussianReal 0 1).prod ν) := by
      have h := hem.symm.integrable_comp_of_integrable hpartialInt
      simpa [rhsProd, Function.comp_def, e, MeasurableEquiv.piFinSuccAbove_symm_apply] using h
    have lhsChange :
        ∫ x, x i * F x ∂(standardGaussianPi (k + 1)) =
          ∫ z, lhsProd z ∂((gaussianReal 0 1).prod ν) := by
      simpa [lhsProd, Function.comp_def, e, Fin.insertNthEquiv] using
        hem.integral_comp' lhsProd
    have rhsChange :
        ∫ x, coordinateDerivative F i x ∂(standardGaussianPi (k + 1)) =
          ∫ z, rhsProd z ∂((gaussianReal 0 1).prod ν) := by
      simpa [rhsProd, Function.comp_def, e, Fin.insertNthEquiv] using
        hem.integral_comp' rhsProd
    have lhsFubini :
        ∫ z, lhsProd z ∂((gaussianReal 0 1).prod ν) =
          ∫ y, ∫ t, t * F (e.symm (t, y)) ∂(gaussianReal 0 1) ∂ν := by
      simpa [lhsProd] using integral_prod_symm lhsProd lhsProdInt
    have rhsFubini :
        ∫ z, rhsProd z ∂((gaussianReal 0 1).prod ν) =
          ∫ y, ∫ t, coordinateDerivative F i (e.symm (t, y))
            ∂(gaussianReal 0 1) ∂ν := by
      simpa [rhsProd] using integral_prod_symm rhsProd rhsProdInt
    have hinner (y : Fin k → ℝ) :
        ∫ t, t * F (e.symm (t, y)) ∂(gaussianReal 0 1) =
          ∫ t, coordinateDerivative F i (e.symm (t, y)) ∂(gaussianReal 0 1) := by
      let base : Fin (k + 1) → ℝ := e.symm (0, y)
      have heq (t : ℝ) : e.symm (t, y) = Function.update base i t := by
        ext j
        by_cases hji : j = i
        · subst j
          simp [base, e, MeasurableEquiv.piFinSuccAbove_symm_apply]
        · have hsucc : ∃ j', i.succAbove j' = j := Fin.exists_succAbove_eq hji
          obtain ⟨j', rfl⟩ := hsucc
          simp [base, e, MeasurableEquiv.piFinSuccAbove_symm_apply, hji]
      have hslice : HasPolynomiallyBoundedDerivative (fun t => F (Function.update base i t)) := by
        constructor
        · exact hF.1.comp (contDiff_update 1 base i)
        · refine ⟨C * (1 + ‖base‖) ^ d, by positivity, d, ?_⟩
          intro t
          have hz := hbound i (Function.update base i t)
          have hder := deriv_update_comp_eq_partial hF.1 base i t
          calc
            |F (Function.update base i t)| +
                |deriv (fun s => F (Function.update base i s)) t|
                ≤ C * (1 + ‖Function.update base i t‖) ^ d := by simpa [hder] using hz
            _ ≤ C * (1 + ‖base‖) ^ d * (1 + |t|) ^ d := by
              have hprod : 1 + ‖Function.update base i t‖ ≤
                  (1 + ‖base‖) * (1 + |t|) := by
                have hn := norm_update_le base i t
                nlinarith [mul_nonneg (norm_nonneg base) (abs_nonneg t)]
              calc
                C * (1 + ‖Function.update base i t‖) ^ d
                    ≤ C * ((1 + ‖base‖) * (1 + |t|)) ^ d := by
                      gcongr
                _ = C * (1 + ‖base‖) ^ d * (1 + |t|) ^ d := by
                      rw [mul_pow]
                      ring
      have hIBP := integral_id_mul_eq_integral_deriv_gaussianReal hslice
      have hleftSlice :
          (fun t => F (Function.update base i t)) = (fun t => F (e.symm (t, y))) := by
        funext t
        rw [heq]
      have hrightSlice (t : ℝ) :
          deriv (fun s => F (Function.update base i s)) t =
            coordinateDerivative F i (e.symm (t, y)) := by
        rw [deriv_update_comp_eq_partial hF.1 base i t]
        rw [← heq t]
      calc
        ∫ t, t * F (e.symm (t, y)) ∂(gaussianReal 0 1)
            = ∫ t, t * F (Function.update base i t) ∂(gaussianReal 0 1) := by
                apply integral_congr_ae
                filter_upwards with t
                rw [heq t]
        _ = ∫ t, deriv (fun s => F (Function.update base i s)) t
            ∂(gaussianReal 0 1) := hIBP
        _ = ∫ t, coordinateDerivative F i (e.symm (t, y))
            ∂(gaussianReal 0 1) := by
              apply integral_congr_ae
              filter_upwards with t
              exact hrightSlice t
    calc
      ∫ x, x i * F x ∂(standardGaussianPi (k + 1))
          = ∫ y, ∫ t, t * F (e.symm (t, y)) ∂(gaussianReal 0 1) ∂ν :=
              lhsChange.trans lhsFubini
      _ = ∫ y, ∫ t, coordinateDerivative F i (e.symm (t, y))
          ∂(gaussianReal 0 1) ∂ν := by
            apply integral_congr_ae
            exact ae_of_all _ hinner
      _ = ∫ x, coordinateDerivative F i x ∂(standardGaussianPi (k + 1)) :=
              (rhsChange.trans rhsFubini).symm

end ASDExplicitGamma.Gaussian
