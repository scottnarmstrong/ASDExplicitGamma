/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import ASDExplicitGamma.Model.Q3Kernel
public import ASDExplicitGamma.Model.Q3Cov
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Exact derivative moments and tensor constants for the q3 kernel
-/

@[expose] public section

namespace ASDExplicitGamma.Model

open MeasureTheory

private noncomputable def q3CovPolynomial : Polynomial ℝ :=
  Polynomial.C 1 - Polynomial.C (39 / 5) * Polynomial.X ^ 2 +
    Polynomial.C (143 / 5) * Polynomial.X ^ 4 -
    Polynomial.C (429 / 5) * Polynomial.X ^ 6 +
    Polynomial.C (429 / 5) * Polynomial.X ^ 7 -
    Polynomial.C (143 / 5) * Polynomial.X ^ 9 +
    Polynomial.C (39 / 5) * Polynomial.X ^ 11 - Polynomial.X ^ 13

private noncomputable def q3CovPositivePolynomial (u : ℝ) : ℝ :=
  Polynomial.eval u q3CovPolynomial

private theorem q3CovPositivePolynomial_eq_formula (u : ℝ) :
    q3CovPositivePolynomial u =
      1 - 39 / 5 * u ^ 2 + 143 / 5 * u ^ 4 - 429 / 5 * u ^ 6 +
        429 / 5 * u ^ 7 - 143 / 5 * u ^ 9 + 39 / 5 * u ^ 11 - u ^ 13 := by
  simp [q3CovPositivePolynomial, q3CovPolynomial, Polynomial.eval_X,
    Polynomial.eval_C]

private theorem q3CovPositivePolynomial_contDiff (n : ℕ) :
    ContDiff ℝ n q3CovPositivePolynomial := by
  rw [show q3CovPositivePolynomial = fun u =>
      1 - 39 / 5 * u ^ 2 + 143 / 5 * u ^ 4 - 429 / 5 * u ^ 6 +
        429 / 5 * u ^ 7 - 143 / 5 * u ^ 9 + 39 / 5 * u ^ 11 - u ^ 13 by
    funext u
    exact q3CovPositivePolynomial_eq_formula u]
  fun_prop

private theorem iteratedDeriv_evalPolynomial (p : Polynomial ℝ) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => Polynomial.eval x p) =
      fun x => Polynomial.eval x ((Polynomial.derivative^[n]) p) := by
  induction n with
  | zero =>
      funext x
      simp [iteratedDeriv_zero]
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by omega, iteratedDeriv_succ, ih]
      funext x
      rw [Function.iterate_succ_apply']
      exact (Polynomial.hasDerivAt (Polynomial.derivative^[n] p) x).deriv

private theorem q3CovPositivePolynomial_iteratedDeriv_two :
    iteratedDeriv 2 q3CovPositivePolynomial 0 = -(78 / 5 : ℝ) := by
  rw [show q3CovPositivePolynomial = fun u => Polynomial.eval u q3CovPolynomial by rfl,
    iteratedDeriv_evalPolynomial]
  change Polynomial.eval 0 ((Polynomial.derivative^[2]) q3CovPolynomial) = -(78 / 5 : ℝ)
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  norm_num [q3CovPolynomial, Polynomial.coeff_X_pow, Polynomial.coeff_C,
    Polynomial.coeff_one]

private theorem q3CovPositivePolynomial_iteratedDeriv_four :
    iteratedDeriv 4 q3CovPositivePolynomial 0 = 3432 / 5 := by
  rw [show q3CovPositivePolynomial = fun u => Polynomial.eval u q3CovPolynomial by rfl,
    iteratedDeriv_evalPolynomial]
  change Polynomial.eval 0 ((Polynomial.derivative^[4]) q3CovPolynomial) = 3432 / 5
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  norm_num [q3CovPolynomial, Polynomial.coeff_X_pow, Polynomial.coeff_C,
    Polynomial.coeff_one]

private theorem q3CovPositivePolynomial_iteratedDeriv_six :
    iteratedDeriv 6 q3CovPositivePolynomial 0 = -(61776 : ℝ) := by
  rw [show q3CovPositivePolynomial = fun u => Polynomial.eval u q3CovPolynomial by rfl,
    iteratedDeriv_evalPolynomial]
  change Polynomial.eval 0 ((Polynomial.derivative^[6]) q3CovPolynomial) = -(61776 : ℝ)
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  norm_num [q3CovPolynomial, Polynomial.coeff_X_pow, Polynomial.coeff_C,
    Polynomial.coeff_one]

private theorem q3CovNegativeSide_contDiff (n : ℕ) :
    ContDiff ℝ n (fun u : ℝ => q3CovPositivePolynomial (-u)) := by
  rw [show (fun u : ℝ => q3CovPositivePolynomial (-u)) =
      (fun u : ℝ => 1 - 39 / 5 * (-u) ^ 2 + 143 / 5 * (-u) ^ 4 -
        429 / 5 * (-u) ^ 6 + 429 / 5 * (-u) ^ 7 - 143 / 5 * (-u) ^ 9 +
        39 / 5 * (-u) ^ 11 - (-u) ^ 13) by
    funext u
    exact q3CovPositivePolynomial_eq_formula (-u)]
  fun_prop

/-- The second right derivative of the q3 covariance at zero. -/
theorem q3Cov_right_iteratedDeriv_two :
    iteratedDerivWithin 2 q3Cov (Set.Icc (0 : ℝ) 1) 0 = -(78 / 5 : ℝ) := by
  have heq : Set.EqOn q3Cov q3CovPositivePolynomial (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    exact (q3Cov_eq_polynomial_on_unit_interval u hu.1 hu.2).trans
      (q3CovPositivePolynomial_eq_formula u).symm
  rw [iteratedDerivWithin_congr heq (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)]
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
    (q3CovPositivePolynomial_contDiff 2).contDiffAt (by norm_num)]
  rw [show q3CovPositivePolynomial = fun u => Polynomial.eval u q3CovPolynomial by rfl,
    iteratedDeriv_evalPolynomial]
  change Polynomial.eval 0 ((Polynomial.derivative^[2]) q3CovPolynomial) = -(78 / 5 : ℝ)
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  norm_num [q3CovPolynomial, Polynomial.coeff_X_pow, Polynomial.coeff_C,
    Polynomial.coeff_one]

/-- The fourth right derivative of the q3 covariance at zero. -/
theorem q3Cov_right_iteratedDeriv_four :
    iteratedDerivWithin 4 q3Cov (Set.Icc (0 : ℝ) 1) 0 = 3432 / 5 := by
  have heq : Set.EqOn q3Cov q3CovPositivePolynomial (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    exact (q3Cov_eq_polynomial_on_unit_interval u hu.1 hu.2).trans
      (q3CovPositivePolynomial_eq_formula u).symm
  rw [iteratedDerivWithin_congr heq (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)]
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
    (q3CovPositivePolynomial_contDiff 4).contDiffAt (by norm_num)]
  rw [show q3CovPositivePolynomial = fun u => Polynomial.eval u q3CovPolynomial by rfl,
    iteratedDeriv_evalPolynomial]
  change Polynomial.eval 0 ((Polynomial.derivative^[4]) q3CovPolynomial) = 3432 / 5
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  norm_num [q3CovPolynomial, Polynomial.coeff_X_pow, Polynomial.coeff_C,
    Polynomial.coeff_one]

/-- The sixth right derivative of the q3 covariance at zero. -/
theorem q3Cov_right_iteratedDeriv_six :
    iteratedDerivWithin 6 q3Cov (Set.Icc (0 : ℝ) 1) 0 = -(61776 : ℝ) := by
  have heq : Set.EqOn q3Cov q3CovPositivePolynomial (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    exact (q3Cov_eq_polynomial_on_unit_interval u hu.1 hu.2).trans
      (q3CovPositivePolynomial_eq_formula u).symm
  rw [iteratedDerivWithin_congr heq (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)]
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
    (q3CovPositivePolynomial_contDiff 6).contDiffAt (by norm_num)]
  rw [show q3CovPositivePolynomial = fun u => Polynomial.eval u q3CovPolynomial by rfl,
    iteratedDeriv_evalPolynomial]
  change Polynomial.eval 0 ((Polynomial.derivative^[6]) q3CovPolynomial) = -(61776 : ℝ)
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  norm_num [q3CovPolynomial, Polynomial.coeff_X_pow, Polynomial.coeff_C,
    Polynomial.coeff_one]

/-- The second left derivative of the even q3 covariance at zero. -/
theorem q3Cov_left_iteratedDeriv_two :
    iteratedDerivWithin 2 q3Cov (Set.Icc (-1 : ℝ) 0) 0 = -(78 / 5 : ℝ) := by
  have heq : Set.EqOn q3Cov (fun u => q3CovPositivePolynomial (-u)) (Set.Icc (-1 : ℝ) 0) := by
    intro u hu
    have hminus : 0 ≤ -u ∧ -u ≤ 1 := by constructor <;> linarith [hu.1, hu.2]
    calc
      q3Cov u = q3Cov (-u) := (q3Cov_even u).symm
      _ = 1 - 39 / 5 * (-u) ^ 2 + 143 / 5 * (-u) ^ 4 - 429 / 5 * (-u) ^ 6 +
          429 / 5 * (-u) ^ 7 - 143 / 5 * (-u) ^ 9 + 39 / 5 * (-u) ^ 11 - (-u) ^ 13 :=
        q3Cov_eq_polynomial_on_unit_interval (-u) hminus.1 hminus.2
      _ = q3CovPositivePolynomial (-u) := (q3CovPositivePolynomial_eq_formula (-u)).symm
  rw [iteratedDerivWithin_congr heq (by norm_num : (0 : ℝ) ∈ Set.Icc (-1) 0)]
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0))
    (q3CovNegativeSide_contDiff 2).contDiffAt (by norm_num)]
  rw [iteratedDeriv_comp_neg]
  simp only [neg_zero]
  rw [q3CovPositivePolynomial_iteratedDeriv_two]
  norm_num

/-- The fourth left derivative of the even q3 covariance at zero. -/
theorem q3Cov_left_iteratedDeriv_four :
    iteratedDerivWithin 4 q3Cov (Set.Icc (-1 : ℝ) 0) 0 = 3432 / 5 := by
  have heq : Set.EqOn q3Cov (fun u => q3CovPositivePolynomial (-u)) (Set.Icc (-1 : ℝ) 0) := by
    intro u hu
    have hminus : 0 ≤ -u ∧ -u ≤ 1 := by constructor <;> linarith [hu.1, hu.2]
    calc
      q3Cov u = q3Cov (-u) := (q3Cov_even u).symm
      _ = 1 - 39 / 5 * (-u) ^ 2 + 143 / 5 * (-u) ^ 4 - 429 / 5 * (-u) ^ 6 +
          429 / 5 * (-u) ^ 7 - 143 / 5 * (-u) ^ 9 + 39 / 5 * (-u) ^ 11 - (-u) ^ 13 :=
        q3Cov_eq_polynomial_on_unit_interval (-u) hminus.1 hminus.2
      _ = q3CovPositivePolynomial (-u) := (q3CovPositivePolynomial_eq_formula (-u)).symm
  rw [iteratedDerivWithin_congr heq (by norm_num : (0 : ℝ) ∈ Set.Icc (-1) 0)]
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0))
    (q3CovNegativeSide_contDiff 4).contDiffAt (by norm_num)]
  rw [iteratedDeriv_comp_neg]
  simp only [neg_zero]
  rw [q3CovPositivePolynomial_iteratedDeriv_four]
  norm_num

/-- The sixth left derivative of the even q3 covariance at zero. -/
theorem q3Cov_left_iteratedDeriv_six :
    iteratedDerivWithin 6 q3Cov (Set.Icc (-1 : ℝ) 0) 0 = -(61776 : ℝ) := by
  have heq : Set.EqOn q3Cov (fun u => q3CovPositivePolynomial (-u)) (Set.Icc (-1 : ℝ) 0) := by
    intro u hu
    have hminus : 0 ≤ -u ∧ -u ≤ 1 := by constructor <;> linarith [hu.1, hu.2]
    calc
      q3Cov u = q3Cov (-u) := (q3Cov_even u).symm
      _ = 1 - 39 / 5 * (-u) ^ 2 + 143 / 5 * (-u) ^ 4 - 429 / 5 * (-u) ^ 6 +
          429 / 5 * (-u) ^ 7 - 143 / 5 * (-u) ^ 9 + 39 / 5 * (-u) ^ 11 - (-u) ^ 13 :=
        q3Cov_eq_polynomial_on_unit_interval (-u) hminus.1 hminus.2
      _ = q3CovPositivePolynomial (-u) := (q3CovPositivePolynomial_eq_formula (-u)).symm
  rw [iteratedDerivWithin_congr heq (by norm_num : (0 : ℝ) ∈ Set.Icc (-1) 0)]
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0))
    (q3CovNegativeSide_contDiff 6).contDiffAt (by norm_num)]
  rw [iteratedDeriv_comp_neg]
  simp only [neg_zero]
  rw [q3CovPositivePolynomial_iteratedDeriv_six]
  norm_num

private def q3MomentD1Polynomial (x : ℝ) : ℝ := -24 * x + 192 * x ^ 3 - 384 * x ^ 5

private def q3MomentD2Polynomial (x : ℝ) : ℝ := -24 + 576 * x ^ 2 - 1920 * x ^ 4

private def q3MomentD3Polynomial (x : ℝ) : ℝ := 1152 * x - 7680 * x ^ 3

private noncomputable def q3MomentD1PrimitivePoly : Polynomial ℝ :=
  Polynomial.C 192 * Polynomial.X ^ 3 - Polynomial.C (9216 / 5) * Polynomial.X ^ 5 +
    Polynomial.C (55296 / 7) * Polynomial.X ^ 7 - Polynomial.C 16384 * Polynomial.X ^ 9 +
    Polynomial.C (147456 / 11) * Polynomial.X ^ 11

private noncomputable def q3MomentD2PrimitivePoly : Polynomial ℝ :=
  Polynomial.C 576 * Polynomial.X - Polynomial.C 9216 * Polynomial.X ^ 3 +
    Polynomial.C (423936 / 5) * Polynomial.X ^ 5 -
    Polynomial.C (2211840 / 7) * Polynomial.X ^ 7 +
    Polynomial.C 409600 * Polynomial.X ^ 9

private noncomputable def q3MomentD3PrimitivePoly : Polynomial ℝ :=
  Polynomial.C 442368 * Polynomial.X ^ 3 - Polynomial.C 3538944 * Polynomial.X ^ 5 +
    Polynomial.C (58982400 / 7) * Polynomial.X ^ 7

private noncomputable def q3MomentD1Primitive (x : ℝ) : ℝ :=
  Polynomial.eval x q3MomentD1PrimitivePoly

private noncomputable def q3MomentD2Primitive (x : ℝ) : ℝ :=
  Polynomial.eval x q3MomentD2PrimitivePoly

private noncomputable def q3MomentD3Primitive (x : ℝ) : ℝ :=
  Polynomial.eval x q3MomentD3PrimitivePoly

private theorem q3MomentD1Primitive_hasDerivAt (x : ℝ) :
    HasDerivAt q3MomentD1Primitive (q3MomentD1Polynomial x ^ 2) x := by
  have h := Polynomial.hasDerivAt q3MomentD1PrimitivePoly x
  convert h using 1
  · rfl
  · simp [q3MomentD1PrimitivePoly, q3MomentD1Polynomial, Polynomial.derivative_C]
    ring

private theorem q3MomentD2Primitive_hasDerivAt (x : ℝ) :
    HasDerivAt q3MomentD2Primitive (q3MomentD2Polynomial x ^ 2) x := by
  have h := Polynomial.hasDerivAt q3MomentD2PrimitivePoly x
  convert h using 1
  · rfl
  · simp [q3MomentD2PrimitivePoly, q3MomentD2Polynomial, Polynomial.derivative_C]
    ring

private theorem q3MomentD3Primitive_hasDerivAt (x : ℝ) :
    HasDerivAt q3MomentD3Primitive (q3MomentD3Polynomial x ^ 2) x := by
  have h := Polynomial.hasDerivAt q3MomentD3PrimitivePoly x
  convert h using 1
  · rfl
  · simp [q3MomentD3PrimitivePoly, q3MomentD3Polynomial, Polynomial.derivative_C]
    ring

private theorem q3MomentD1Polynomial_sq_integral :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), q3MomentD1Polynomial x ^ 2 = 2048 / 385 := by
  calc
    _ = q3MomentD1Primitive (1 / 2) - q3MomentD1Primitive (-(1 / 2 : ℝ)) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        exact q3MomentD1Primitive_hasDerivAt x
      · have hcont : Continuous (fun x : ℝ => q3MomentD1Polynomial x ^ 2) := by
          change Continuous (fun x : ℝ => (-24 * x + 192 * x ^ 3 - 384 * x ^ 5) ^ 2)
          fun_prop
        exact hcont.intervalIntegrable _ _
    _ = 2048 / 385 := by norm_num [q3MomentD1Primitive, q3MomentD1PrimitivePoly]

private theorem q3MomentD2Polynomial_sq_integral :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), q3MomentD2Polynomial x ^ 2 = 8192 / 35 := by
  calc
    _ = q3MomentD2Primitive (1 / 2) - q3MomentD2Primitive (-(1 / 2 : ℝ)) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        exact q3MomentD2Primitive_hasDerivAt x
      · have hcont : Continuous (fun x : ℝ => q3MomentD2Polynomial x ^ 2) := by
          change Continuous (fun x : ℝ => (-24 + 576 * x ^ 2 - 1920 * x ^ 4) ^ 2)
          fun_prop
        exact hcont.intervalIntegrable _ _
    _ = 8192 / 35 := by norm_num [q3MomentD2Primitive, q3MomentD2PrimitivePoly]

private theorem q3MomentD3Polynomial_sq_integral :
    ∫ x in (-(1 / 2 : ℝ))..(1 / 2), q3MomentD3Polynomial x ^ 2 = 147456 / 7 := by
  calc
    _ = q3MomentD3Primitive (1 / 2) - q3MomentD3Primitive (-(1 / 2 : ℝ)) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        exact q3MomentD3Primitive_hasDerivAt x
      · have hcont : Continuous (fun x : ℝ => q3MomentD3Polynomial x ^ 2) := by
          change Continuous (fun x : ℝ => (1152 * x - 7680 * x ^ 3) ^ 2)
          fun_prop
        exact hcont.intervalIntegrable _ _
    _ = 147456 / 7 := by norm_num [q3MomentD3Primitive, q3MomentD3PrimitivePoly]

private theorem q3KernelD1_sq_eq_indicator (x : ℝ) :
    q3KernelD1 x ^ 2 = Set.indicator (Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
      (fun x => (Real.sqrt (3003 / 1024)) ^ 2 * q3MomentD1Polynomial x ^ 2) x := by
  by_cases hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)
  · rw [Set.indicator_of_mem hx]
    have hpos : 0 ≤ 1 - 4 * x ^ 2 := by
      have hx' : |x| ≤ 1 / 2 := abs_le.mpr hx
      have hprod : 0 ≤ (1 / 2 - |x|) * (1 / 2 + |x|) :=
        mul_nonneg (sub_nonneg.mpr hx') (by positivity)
      nlinarith [sq_abs x]
    rw [q3KernelD1, max_eq_left hpos]
    simp only [q3MomentD1Polynomial]
    ring
  · rw [Set.indicator_of_notMem hx]
    have hbound : 1 / 2 ≤ |x| := by
      by_contra h
      exact hx (abs_le.mp (le_of_not_ge h))
    have hzero : q3KernelD1 x = 0 := by
      rw [q3KernelD1, max_eq_right (show 1 - 4 * x ^ 2 ≤ 0 by nlinarith [sq_abs x])]
      ring
    simp [hzero]

private theorem q3KernelD2_sq_eq_indicator (x : ℝ) :
    q3KernelD2 x ^ 2 = Set.indicator (Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
      (fun x => (Real.sqrt (3003 / 1024)) ^ 2 * q3MomentD2Polynomial x ^ 2) x := by
  by_cases hx : x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)
  · rw [Set.indicator_of_mem hx]
    have hpos : 0 ≤ 1 - 4 * x ^ 2 := by
      have hx' : |x| ≤ 1 / 2 := abs_le.mpr hx
      have hprod : 0 ≤ (1 / 2 - |x|) * (1 / 2 + |x|) :=
        mul_nonneg (sub_nonneg.mpr hx') (by positivity)
      nlinarith [sq_abs x]
    rw [q3KernelD2, max_eq_left hpos]
    simp only [q3MomentD2Polynomial]
    ring
  · rw [Set.indicator_of_notMem hx]
    have hbound : 1 / 2 ≤ |x| := by
      by_contra h
      exact hx (abs_le.mp (le_of_not_ge h))
    have hzero : q3KernelD2 x = 0 := by
      rw [q3KernelD2, max_eq_right (show 1 - 4 * x ^ 2 ≤ 0 by nlinarith [sq_abs x])]
      ring
    simp [hzero]

private theorem q3KernelD3_sq_eq_indicator (x : ℝ) :
    q3KernelD3 x ^ 2 = Set.indicator (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))
      (fun x => (Real.sqrt (3003 / 1024)) ^ 2 * q3MomentD3Polynomial x ^ 2) x := by
  by_cases hx : x ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)
  · rw [Set.indicator_of_mem hx, q3KernelD3]
    have habs : |x| < 1 / 2 := abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    split_ifs with h
    · simp only [q3MomentD3Polynomial]
      ring
    · exact False.elim (h habs)
  · rw [Set.indicator_of_notMem hx, q3KernelD3]
    split_ifs with h
    · exact False.elim (hx (by
        have h' := abs_lt.mp h
        exact ⟨by linarith [h'.1], by linarith [h'.2]⟩))
    · norm_num

private theorem q3KernelD1_sq_integral : ∫ x, q3KernelD1 x ^ 2 = 78 / 5 := by
  calc
    _ = ∫ x, Set.indicator (Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
        (fun x => (Real.sqrt (3003 / 1024)) ^ 2 * q3MomentD1Polynomial x ^ 2) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact q3KernelD1_sq_eq_indicator x
    _ = ∫ x in Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
        (Real.sqrt (3003 / 1024)) ^ 2 * q3MomentD1Polynomial x ^ 2 := by
      rw [integral_indicator measurableSet_Icc]
    _ = ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        (Real.sqrt (3003 / 1024)) ^ 2 * q3MomentD1Polynomial x ^ 2 := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    _ = (Real.sqrt (3003 / 1024)) ^ 2 *
        ∫ x in (-(1 / 2 : ℝ))..(1 / 2), q3MomentD1Polynomial x ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ = 78 / 5 := by
      rw [q3MomentD1Polynomial_sq_integral, Real.sq_sqrt (by norm_num : 0 ≤ (3003 / 1024 : ℝ))]
      norm_num

private theorem q3KernelD2_sq_integral : ∫ x, q3KernelD2 x ^ 2 = 3432 / 5 := by
  calc
    _ = ∫ x, Set.indicator (Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
        (fun x => (Real.sqrt (3003 / 1024)) ^ 2 * q3MomentD2Polynomial x ^ 2) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact q3KernelD2_sq_eq_indicator x
    _ = ∫ x in Set.Icc (-(1 / 2 : ℝ)) (1 / 2),
        (Real.sqrt (3003 / 1024)) ^ 2 * q3MomentD2Polynomial x ^ 2 := by
      rw [integral_indicator measurableSet_Icc]
    _ = ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        (Real.sqrt (3003 / 1024)) ^ 2 * q3MomentD2Polynomial x ^ 2 := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    _ = (Real.sqrt (3003 / 1024)) ^ 2 *
        ∫ x in (-(1 / 2 : ℝ))..(1 / 2), q3MomentD2Polynomial x ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ = 3432 / 5 := by
      rw [q3MomentD2Polynomial_sq_integral, Real.sq_sqrt (by norm_num : 0 ≤ (3003 / 1024 : ℝ))]
      norm_num

private theorem q3KernelD3_sq_integral : ∫ x, q3KernelD3 x ^ 2 = 61776 := by
  calc
    _ = ∫ x, Set.indicator (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))
        (fun x => (Real.sqrt (3003 / 1024)) ^ 2 * q3MomentD3Polynomial x ^ 2) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact q3KernelD3_sq_eq_indicator x
    _ = ∫ x in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2),
        (Real.sqrt (3003 / 1024)) ^ 2 * q3MomentD3Polynomial x ^ 2 := by
      rw [integral_indicator measurableSet_Ioo]
    _ = ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        (Real.sqrt (3003 / 1024)) ^ 2 * q3MomentD3Polynomial x ^ 2 := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
    _ = (Real.sqrt (3003 / 1024)) ^ 2 *
        ∫ x in (-(1 / 2 : ℝ))..(1 / 2), q3MomentD3Polynomial x ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
    _ = 61776 := by
      rw [q3MomentD3Polynomial_sq_integral, Real.sq_sqrt (by norm_num : 0 ≤ (3003 / 1024 : ℝ))]
      norm_num

/-- The exact squared integral of the first derivative of the q3 kernel. -/
theorem q3KernelD1_sq_integral_exact : ∫ x, q3KernelD1 x ^ 2 = 78 / 5 :=
  q3KernelD1_sq_integral

/-- The exact squared integral of the second derivative of the q3 kernel. -/
theorem q3KernelD2_sq_integral_exact : ∫ x, q3KernelD2 x ^ 2 = 3432 / 5 :=
  q3KernelD2_sq_integral

/-- The exact squared integral of the piecewise third-derivative representative. -/
theorem q3KernelD3_sq_integral_exact : ∫ x, q3KernelD3 x ^ 2 = 61776 :=
  q3KernelD3_sq_integral

/-- Reflection of the frozen q3 kernel, used in the autocorrelation convolution. -/
noncomputable def q3KernelReflection (x : ℝ) : ℝ := q3Kernel (-x)

/-- The convolution of the q3 kernel with its reflection. -/
noncomputable def q3KernelConvolution (u : ℝ) : ℝ :=
  ∫ y : ℝ, q3Kernel y * q3KernelReflection (u - y)

/-- The frozen covariance is exactly the q3 kernel convolved with its reflection. -/
theorem q3Cov_eq_q3KernelConvolution (u : ℝ) :
    q3Cov u = q3KernelConvolution u := by
  rw [← q3Cov_even u]
  rw [q3Cov, q3KernelConvolution]
  change (∫ y : ℝ, q3Kernel y * q3Kernel (y - u)) =
    ∫ y : ℝ, q3Kernel y * q3Kernel (-(u - y))
  apply integral_congr_ae
  filter_upwards [] with y
  congr 2
  ring

/-- The covariance derivatives at zero agree with the three squared derivative norms. -/
theorem q3Cov_right_derivative_norm_identities :
    -(iteratedDerivWithin 2 q3Cov (Set.Icc (0 : ℝ) 1) 0) = ∫ x, q3KernelD1 x ^ 2 ∧
      iteratedDerivWithin 4 q3Cov (Set.Icc (0 : ℝ) 1) 0 = ∫ x, q3KernelD2 x ^ 2 ∧
      -(iteratedDerivWithin 6 q3Cov (Set.Icc (0 : ℝ) 1) 0) = ∫ x, q3KernelD3 x ^ 2 := by
  rw [q3Cov_right_iteratedDeriv_two, q3KernelD1_sq_integral_exact,
    q3Cov_right_iteratedDeriv_four, q3KernelD2_sq_integral_exact,
    q3Cov_right_iteratedDeriv_six, q3KernelD3_sq_integral_exact]
  norm_num

/-- The matching left-side covariance derivatives have the same three norm values. -/
theorem q3Cov_left_derivative_norm_identities :
    -(iteratedDerivWithin 2 q3Cov (Set.Icc (-1 : ℝ) 0) 0) = ∫ x, q3KernelD1 x ^ 2 ∧
      iteratedDerivWithin 4 q3Cov (Set.Icc (-1 : ℝ) 0) 0 = ∫ x, q3KernelD2 x ^ 2 ∧
      -(iteratedDerivWithin 6 q3Cov (Set.Icc (-1 : ℝ) 0) 0) = ∫ x, q3KernelD3 x ^ 2 := by
  rw [q3Cov_left_iteratedDeriv_two, q3KernelD1_sq_integral_exact,
    q3Cov_left_iteratedDeriv_four, q3KernelD2_sq_integral_exact,
    q3Cov_left_iteratedDeriv_six, q3KernelD3_sq_integral_exact]
  norm_num

/-- The first one-dimensional derivative variance moment. -/
def q3r1 : ℚ := 78 / 5

/-- The second one-dimensional derivative variance moment. -/
def q3r2 : ℚ := 3432 / 5

/-- The third one-dimensional derivative variance moment. -/
def q3r3 : ℚ := 61776

/-- The order-one two-coordinate tensor moment. -/
def q3mu1 : ℚ := 2 * q3r1

/-- The order-two two-coordinate tensor moment. -/
def q3mu2 : ℚ := 2 * q3r2 + 2 * q3r1 ^ 2

/-- The order-three two-coordinate tensor moment. -/
def q3mu3 : ℚ := 2 * q3r3 + 6 * q3r1 * q3r2

/-- The heat constants are twice the corresponding derivative tensor moments. -/
def q3tau (i : Fin 3) : ℚ := 2 * (if i = 0 then q3mu1 else if i = 1 then q3mu2 else q3mu3)

/-- The separable two-coordinate product covariance `c(x₀)c(x₁)`. -/
noncomputable def q3ProductCovariance (x : Fin 2 → ℝ) : ℝ :=
  q3Cov (x 0) * q3Cov (x 1)

/-- Exact rational value of the first derivative variance moment. -/
theorem q3r1_exact : q3r1 = 78 / 5 := by norm_num [q3r1]

/-- Exact rational value of the second derivative variance moment. -/
theorem q3r2_exact : q3r2 = 3432 / 5 := by norm_num [q3r2]

/-- Exact rational value of the third derivative variance moment. -/
theorem q3r3_exact : q3r3 = 61776 := by norm_num [q3r3]

/-- The rational derivative moments are the sign-adjusted even covariance derivatives at zero. -/
theorem q3r_covariance_derivative_values :
    (q3r1 : ℝ) = -(iteratedDerivWithin 2 q3Cov (Set.Icc (0 : ℝ) 1) 0) ∧
      (q3r2 : ℝ) = iteratedDerivWithin 4 q3Cov (Set.Icc (0 : ℝ) 1) 0 ∧
      (q3r3 : ℝ) = -(iteratedDerivWithin 6 q3Cov (Set.Icc (0 : ℝ) 1) 0) := by
  rw [q3Cov_right_iteratedDeriv_two, q3Cov_right_iteratedDeriv_four,
    q3Cov_right_iteratedDeriv_six]
  norm_num [q3r1, q3r2, q3r3]

/-- Exact rational value of the first tensor moment. -/
theorem q3mu1_exact : q3mu1 = 156 / 5 := by norm_num [q3mu1, q3r1]

/-- Exact rational value of the second tensor moment. -/
theorem q3mu2_exact : q3mu2 = 46488 / 25 := by norm_num [q3mu2, q3r1, q3r2]

/-- Exact rational value of the third tensor moment. -/
theorem q3mu3_exact : q3mu3 = 4694976 / 25 := by norm_num [q3mu3, q3r1, q3r2, q3r3]

/-- Exact heat constants, in increasing derivative order. -/
theorem q3tau_exact : q3tau 0 = 312 / 5 ∧ q3tau 1 = 92976 / 25 ∧
    q3tau 2 = 9389952 / 25 := by
  norm_num [q3tau, q3mu1, q3mu2, q3mu3, q3r1, q3r2, q3r3]

/-- Order-one component variance for the separable product covariance `c(x₀)c(x₁)`. -/
def q3PartialVarianceOne (_i : Fin 2) : ℚ := q3r1

/-- Order-two component variance: a repeated coordinate contributes `r₂`, and a mixed pair `r₁²`. -/
def q3PartialVarianceTwo (i : Fin 2 × Fin 2) : ℚ :=
  if i.1 = i.2 then q3r2 else q3r1 ^ 2

/-- Order-three component variance: one coordinate repeated thrice contributes `r₃`; a split contributes `r₁r₂`. -/
def q3PartialVarianceThree (i : Fin 2 × Fin 2 × Fin 2) : ℚ :=
  if i.1 = i.2.1 ∧ i.2.1 = i.2.2 then q3r3 else q3r1 * q3r2

/-- Sum of the order-one partial derivative component variances. -/
theorem q3PartialVarianceOne_sum :
    (∑ i : Fin 2, q3PartialVarianceOne i) = q3mu1 := by
  norm_num [q3PartialVarianceOne, q3mu1, q3r1]

/-- Sum of the order-two partial derivative component variances. -/
theorem q3PartialVarianceTwo_sum :
    (∑ i : Fin 2 × Fin 2, q3PartialVarianceTwo i) = q3mu2 := by
  norm_num [q3PartialVarianceTwo, q3mu2, q3r1, q3r2, Fintype.sum_prod_type]

/-- Sum of the order-three partial derivative component variances. -/
theorem q3PartialVarianceThree_sum :
    (∑ i : Fin 2 × Fin 2 × Fin 2, q3PartialVarianceThree i) = q3mu3 := by
  norm_num [q3PartialVarianceThree, q3mu3, q3r1, q3r2, q3r3, Fintype.sum_prod_type]

end ASDExplicitGamma.Model

end
