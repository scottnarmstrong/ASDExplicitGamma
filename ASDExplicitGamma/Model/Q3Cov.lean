/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import ASDExplicitGamma.Statements.Q3Cov
public import ASDExplicitGamma.Model.Q3Kernel
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Exact covariance identities for the q3 kernel

This module reduces the frozen autocovariance to an interval integral and evaluates that integral
as an exact polynomial on the nonnegative unit interval.
-/

@[expose] public section

namespace ASDExplicitGamma.Model

open MeasureTheory

private theorem q3Kernel_even (x : ℝ) : q3Kernel (-x) = q3Kernel x := by
  rw [q3Kernel, q3Kernel]
  simp only [abs_neg, neg_sq]

private theorem q3Kernel_nonzero_bound {x : ℝ} (hx : q3Kernel x ≠ 0) : |x| ≤ 1 / 2 := by
  by_contra h
  have hge : 1 / 2 ≤ |x| := le_of_not_ge h
  exact hx (q3Kernel_eq_zero_of_abs_ge hge)

/-- The frozen q3 covariance is even. -/
theorem q3Cov_even (u : ℝ) : q3Cov (-u) = q3Cov u := by
  rw [q3Cov, q3Cov]
  have hchange :
      (∫ y : ℝ, q3Kernel y * q3Kernel (y - u)) =
        |(-1 : ℝ)⁻¹| • ∫ z : ℝ, q3Kernel (-z) * q3Kernel (-z - u) := by
    simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
      (Measure.integral_comp_mul_left
        (fun z : ℝ => q3Kernel (-z) * q3Kernel (-z - u)) (-1))
  calc
    (∫ y : ℝ, q3Kernel y * q3Kernel (y - u)) =
        |(-1 : ℝ)⁻¹| • ∫ z : ℝ, q3Kernel (-z) * q3Kernel (-z - u) := hchange
    _ = ∫ z : ℝ, q3Kernel z * q3Kernel (z + u) := by
      norm_num
      apply integral_congr_ae
      filter_upwards [] with z
      rw [q3Kernel_even z, show -z - u = -(z + u) by ring, q3Kernel_even (z + u)]

/-- The covariance vanishes once the two translated kernel supports no longer overlap. -/
theorem q3Cov_zero_of_abs_ge_one {u : ℝ} (hu : 1 ≤ |u|) : q3Cov u = 0 := by
  rw [q3Cov]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : q3Kernel y = 0
  · simp [hy]
  · have hybound := q3Kernel_nonzero_bound hy
    have hu_pos : 1 ≤ u ∨ u ≤ -1 := by
      rcases le_total 0 u with hle | hle
      · left
        rw [abs_of_nonneg hle] at hu
        exact hu
      · right
        rw [abs_of_nonpos hle] at hu
        linarith
    rcases hu_pos with hpos | hneg
    · have hshift : 1 / 2 ≤ |y + u| := by
        have hylower := (abs_le.mp hybound).1
        rw [abs_of_nonneg (by linarith [hylower])]
        linarith [hylower]
      simp [q3Kernel_eq_zero_of_abs_ge hshift]
    · have hshift : 1 / 2 ≤ |y + u| := by
        have hyupper := (abs_le.mp hybound).2
        rw [abs_of_nonpos (by linarith [hyupper])]
        linarith [hyupper]
      simp [q3Kernel_eq_zero_of_abs_ge hshift]

/-- For `0 ≤ u ≤ 1`, the covariance integral is supported on the overlap interval. -/
theorem q3Cov_eq_overlap_integral {u : ℝ} (hu0 : 0 ≤ u) :
    q3Cov u = ∫ y in (-(1 / 2 : ℝ))..(1 / 2 - u),
      q3Kernel y * q3Kernel (y + u) := by
  let f : ℝ → ℝ := fun y => q3Kernel y * q3Kernel (y + u)
  have hsupp : Function.support f ⊆ Set.Ioc (-1) 1 := by
    intro y hy
    have hq : q3Kernel y ≠ 0 := by
      intro hzero
      apply hy
      simp [f, hzero]
    have hb := q3Kernel_nonzero_bound hq
    constructor <;> have := abs_le.mp hb <;> nlinarith
  have hfull : ∫ y : ℝ, f y = ∫ y in (-1 : ℝ)..1, f y :=
    (intervalIntegral.integral_eq_integral_of_support_subset hsupp).symm
  have hcont : Continuous f := by
    dsimp [f]
    exact q3Kernel_continuous.mul (q3Kernel_continuous.comp (continuous_id.add continuous_const))
  have hleft : ∫ y in (-1 : ℝ)..(-(1 / 2 : ℝ)), f y = 0 := by
    calc
      ∫ y in (-1 : ℝ)..(-(1 / 2 : ℝ)), f y = ∫ _y in (-1 : ℝ)..(-(1 / 2 : ℝ)), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [Set.uIcc_of_le (by norm_num)] at hy
        dsimp [f]
        have habs : 1 / 2 ≤ |y| := by
          rw [abs_of_nonpos (le_trans hy.2 (by norm_num))]
          nlinarith [hy.2]
        simp [q3Kernel_eq_zero_of_abs_ge habs]
      _ = 0 := by simp
  have hright : ∫ y in (1 / 2 - u)..1, f y = 0 := by
    calc
      ∫ y in (1 / 2 - u)..1, f y = ∫ _y in (1 / 2 - u)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [Set.uIcc_of_le (by linarith : 1 / 2 - u ≤ 1)] at hy
        dsimp [f]
        have hyu : 1 / 2 ≤ y + u := by linarith [hy.1]
        have hyu_nonneg : 0 ≤ y + u := le_trans (by norm_num) hyu
        have hshift : 1 / 2 ≤ |y + u| := by rw [abs_of_nonneg hyu_nonneg]; exact hyu
        simp [q3Kernel_eq_zero_of_abs_ge hshift]
      _ = 0 := by simp
  have hjoin₁ :
      (∫ y in (-1 : ℝ)..(-(1 / 2 : ℝ)), f y) +
        ∫ y in (-(1 / 2 : ℝ))..1, f y = ∫ y in (-1 : ℝ)..1, f y := by
    exact intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (-1) (-(1 / 2 : ℝ)))
      (hcont.intervalIntegrable (-(1 / 2 : ℝ)) 1)
  have hjoin₂ :
      (∫ y in (-(1 / 2 : ℝ))..(1 / 2 - u), f y) +
        ∫ y in (1 / 2 - u)..1, f y = ∫ y in (-(1 / 2 : ℝ))..1, f y := by
    exact intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (-(1 / 2 : ℝ)) (1 / 2 - u))
      (hcont.intervalIntegrable (1 / 2 - u) 1)
  rw [q3Cov]
  change ∫ y : ℝ, f y = ∫ y in (-(1 / 2 : ℝ))..(1 / 2 - u), f y
  calc
    ∫ y : ℝ, f y = ∫ y in (-1 : ℝ)..1, f y := hfull
    _ = ∫ y in (-(1 / 2 : ℝ))..1, f y := by
      rw [← hjoin₁, hleft]
      simp
    _ = ∫ y in (-(1 / 2 : ℝ))..(1 / 2 - u), f y := by
      rw [← hjoin₂, hright]
      simp

private noncomputable def q3CovPrimitivePoly (u : ℝ) : Polynomial ℝ :=
  Polynomial.C (1 - 12 * u ^ 2 + 48 * u ^ 4 - 64 * u ^ 6) * Polynomial.X -
    Polynomial.C (12 * u - 96 * u ^ 3 + 192 * u ^ 5) * Polynomial.X ^ 2 +
    Polynomial.C (-8 + 144 * u ^ 2 - 512 * u ^ 4 + 256 * u ^ 6) * Polynomial.X ^ 3 +
    Polynomial.C (120 * u - 896 * u ^ 3 + 1152 * u ^ 5) * Polynomial.X ^ 4 +
    Polynomial.C (48 - 4992 * u ^ 2 / 5 + 13824 * u ^ 4 / 5 - 3072 * u ^ 6 / 5) * Polynomial.X ^ 5 +
    Polynomial.C (-640 * u + 4096 * u ^ 3 - 3072 * u ^ 5) * Polynomial.X ^ 6 +
    Polynomial.C (-1280 / 7 + 26112 * u ^ 2 / 7 - 49152 * u ^ 4 / 7 + 4096 * u ^ 6 / 7) * Polynomial.X ^ 7 +
    Polynomial.C (1920 * u - 9216 * u ^ 3 + 3072 * u ^ 5) * Polynomial.X ^ 8 +
    Polynomial.C (1280 / 3 - 7168 * u ^ 2 + 20480 * u ^ 4 / 3) * Polynomial.X ^ 9 +
    Polynomial.C (-3072 * u + 8192 * u ^ 3) * Polynomial.X ^ 10 +
    Polynomial.C (-6144 / 11 + 61440 * u ^ 2 / 11) * Polynomial.X ^ 11 +
    Polynomial.C (2048 * u) * Polynomial.X ^ 12 +
    Polynomial.C (4096 / 13) * Polynomial.X ^ 13

private noncomputable def q3CovPrimitive (u y : ℝ) : ℝ :=
  Polynomial.eval y (q3CovPrimitivePoly u)

private theorem q3CovPrimitive_hasDerivAt (u y : ℝ) :
    HasDerivAt (q3CovPrimitive u)
      ((1 - 4 * y ^ 2) ^ 3 * (1 - 4 * (y + u) ^ 2) ^ 3) y := by
  have h := Polynomial.hasDerivAt (q3CovPrimitivePoly u) y
  convert h using 1
  · rfl
  · simp [q3CovPrimitivePoly, Polynomial.derivative_X, Polynomial.derivative_C,
      Polynomial.derivative_pow]
    ring

private theorem q3Cov_polynomial_interval_integral (u : ℝ) :
    ∫ y in (-(1 / 2 : ℝ))..(1 / 2 - u),
        (1 - 4 * y ^ 2) ^ 3 * (1 - 4 * (y + u) ^ 2) ^ 3 =
      q3CovPrimitive u (1 / 2 - u) - q3CovPrimitive u (-(1 / 2 : ℝ)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    exact q3CovPrimitive_hasDerivAt u y
  · have hcont : Continuous (fun y : ℝ => (1 - 4 * y ^ 2) ^ 3 *
      (1 - 4 * (y + u) ^ 2) ^ 3) := by fun_prop
    exact hcont.intervalIntegrable (-(1 / 2 : ℝ)) (1 / 2 - u)

/-- The exact positive-side polynomial formula for the frozen q3 covariance. -/
theorem q3Cov_eq_polynomial_on_unit_interval (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    q3Cov u = 1 - 39 / 5 * u ^ 2 + 143 / 5 * u ^ 4 - 429 / 5 * u ^ 6 +
      429 / 5 * u ^ 7 - 143 / 5 * u ^ 9 + 39 / 5 * u ^ 11 - u ^ 13 := by
  rw [q3Cov_eq_overlap_integral hu0]
  have hpoint : Set.EqOn
      (fun y : ℝ => q3Kernel y * q3Kernel (y + u))
      (fun y => (Real.sqrt (3003 / 1024)) ^ 2 *
        ((1 - 4 * y ^ 2) ^ 3 * (1 - 4 * (y + u) ^ 2) ^ 3))
      (Set.uIcc (-(1 / 2 : ℝ)) (1 / 2 - u)) := by
    intro y hy
    rw [Set.uIcc_of_le (by linarith : -(1 / 2 : ℝ) ≤ 1 / 2 - u)] at hy
    have hybound : |y| ≤ 1 / 2 := by
      apply abs_le.mpr
      constructor
      · linarith [hy.1]
      · linarith [hy.2, hu0]
    have hyshift : |y + u| ≤ 1 / 2 := by
      apply abs_le.mpr
      constructor
      · linarith [hy.1]
      · linarith [hy.2]
    have hypos : 0 ≤ 1 - 4 * y ^ 2 := by
      have hprod : 0 ≤ (1 / 2 - |y|) * (1 / 2 + |y|) :=
        mul_nonneg (sub_nonneg.mpr hybound) (by positivity)
      nlinarith [sq_abs y]
    have hyshiftpos : 0 ≤ 1 - 4 * (y + u) ^ 2 := by
      have hprod : 0 ≤ (1 / 2 - |y + u|) * (1 / 2 + |y + u|) :=
        mul_nonneg (sub_nonneg.mpr hyshift) (by positivity)
      nlinarith [sq_abs (y + u)]
    change q3Kernel y * q3Kernel (y + u) =
      (Real.sqrt (3003 / 1024)) ^ 2 *
        ((1 - 4 * y ^ 2) ^ 3 * (1 - 4 * (y + u) ^ 2) ^ 3)
    rw [q3Kernel_eq_positive_part, max_eq_left hypos,
      q3Kernel_eq_positive_part, max_eq_left hyshiftpos]
    ring
  have hmid :
      ∫ y in (-(1 / 2 : ℝ))..(1 / 2 - u), q3Kernel y * q3Kernel (y + u) =
        (Real.sqrt (3003 / 1024)) ^ 2 *
          ∫ y in (-(1 / 2 : ℝ))..(1 / 2 - u),
            (1 - 4 * y ^ 2) ^ 3 * (1 - 4 * (y + u) ^ 2) ^ 3 := by
    calc
      _ = ∫ y in (-(1 / 2 : ℝ))..(1 / 2 - u),
          (Real.sqrt (3003 / 1024)) ^ 2 *
            ((1 - 4 * y ^ 2) ^ 3 * (1 - 4 * (y + u) ^ 2) ^ 3) :=
        intervalIntegral.integral_congr hpoint
      _ = (Real.sqrt (3003 / 1024)) ^ 2 *
          ∫ y in (-(1 / 2 : ℝ))..(1 / 2 - u),
            (1 - 4 * y ^ 2) ^ 3 * (1 - 4 * (y + u) ^ 2) ^ 3 :=
        intervalIntegral.integral_const_mul _ _
  have hprimitive := q3Cov_polynomial_interval_integral u
  have hsqrt : (Real.sqrt (3003 / 1024 : ℝ)) ^ 2 = 3003 / 1024 :=
    Real.sq_sqrt (by norm_num)
  rw [hmid, hprimitive, hsqrt]
  norm_num [q3CovPrimitive, q3CovPrimitivePoly]
  ring

end ASDExplicitGamma.Model

end
