/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import ASDExplicitGamma.Statements.Q3Kernel
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Regularity and exact moments of the q3 kernel

The frozen kernel is the compactly supported cubic cutoff from the source. This module proves its
support, continuity, and integral identities used by the q3 covariance calculations.
-/

@[expose] public section

namespace ASDExplicitGamma.Model

open MeasureTheory

/-- The positive-part expression for the frozen q3 kernel. -/
theorem q3Kernel_eq_positive_part (x : ℝ) :
    q3Kernel x = Real.sqrt (3003 / 1024) * max (1 - 4 * x ^ 2) 0 ^ 3 := by
  by_cases hx : |x| ≤ 1 / 2
  · have hsquare : x ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      have hx' := abs_le.mp hx
      nlinarith
    have hpos : 0 ≤ 1 - 4 * x ^ 2 := by nlinarith
    rw [q3Kernel, ite_eq_left hx, max_eq_left hpos]
  · have hneg : 1 - 4 * x ^ 2 ≤ 0 := by
      have hx' : (1 / 2 : ℝ) < |x| := lt_of_not_ge hx
      nlinarith [sq_abs x]
    rw [q3Kernel, ite_eq_right hx, max_eq_right hneg]
    norm_num

/-- On the open support, the frozen q3 kernel is its defining polynomial. -/
theorem q3Kernel_eq_polynomial_inside {x : ℝ} (hx : |x| < 1 / 2) :
    q3Kernel x = Real.sqrt (3003 / 1024) * (1 - 4 * x ^ 2) ^ 3 := by
  rw [q3Kernel_eq_positive_part]
  have hpos : 0 ≤ 1 - 4 * x ^ 2 := by
    have hx' := abs_lt.mp hx
    nlinarith
  rw [max_eq_left hpos]

private def q3PositiveSquare (x : ℝ) : ℝ := (max x 0) ^ 2

private def q3PositiveCube (x : ℝ) : ℝ := (max x 0) ^ 3

private theorem q3PositiveSquare_hasDerivAt (x : ℝ) :
    HasDerivAt q3PositiveSquare (2 * max x 0) x := by
  by_cases hx0 : x < 0
  · have heq : q3PositiveSquare =ᶠ[nhds x] fun _ : ℝ => (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds hx0] with y hy
      simp [q3PositiveSquare, max_eq_right (le_of_lt hy)]
    have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x := hasDerivAt_const x (0 : ℝ)
    have hzero : 2 * max x 0 = 0 := by simp [max_eq_right hx0.le]
    simpa [hzero] using hconst.congr_of_eventuallyEq heq
  · by_cases hxpos : 0 < x
    · have heq : q3PositiveSquare =ᶠ[nhds x] fun y : ℝ => y ^ 2 := by
        filter_upwards [eventually_gt_nhds hxpos] with y hy
        simp [q3PositiveSquare, max_eq_left hy.le]
      have hpoly : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        convert (hasDerivAt_pow 2 x) using 1; ring
      have hres := hpoly.congr_of_eventuallyEq heq
      convert hres using 1; simp [max_eq_left hxpos.le]
    · have hx : x = 0 := le_antisymm (le_of_not_gt hxpos) (le_of_not_gt hx0)
      subst x
      rw [hasDerivAt_iff_tendsto_slope]
      have heq : (fun y : ℝ => slope q3PositiveSquare 0 y) =ᶠ[nhdsWithin 0 ({0}ᶜ)]
          fun y => max y 0 := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy0 : y ≠ 0 := hy
        by_cases h : 0 ≤ y
        · simp [slope, q3PositiveSquare, max_eq_left h]; field_simp [hy0]
        · simp [slope, q3PositiveSquare, max_eq_right (le_of_not_ge h)]
      have hcont : ContinuousAt (fun y : ℝ => max y 0) 0 :=
        (continuous_id.max continuous_const).continuousAt
      simpa using (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm

private theorem q3PositiveCube_hasDerivAt (x : ℝ) :
    HasDerivAt q3PositiveCube (3 * (max x 0) ^ 2) x := by
  by_cases hx0 : x < 0
  · have heq : q3PositiveCube =ᶠ[nhds x] fun _ : ℝ => (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds hx0] with y hy
      simp [q3PositiveCube, max_eq_right (le_of_lt hy)]
    have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x := hasDerivAt_const x (0 : ℝ)
    have hzero : 3 * (max x 0) ^ 2 = 0 := by simp [max_eq_right hx0.le]
    simpa [hzero] using hconst.congr_of_eventuallyEq heq
  · by_cases hxpos : 0 < x
    · have heq : q3PositiveCube =ᶠ[nhds x] fun y : ℝ => y ^ 3 := by
        filter_upwards [eventually_gt_nhds hxpos] with y hy
        simp [q3PositiveCube, max_eq_left hy.le]
      have hpoly : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
        convert (hasDerivAt_pow 3 x) using 1
      have hres := hpoly.congr_of_eventuallyEq heq
      convert hres using 1; simp [max_eq_left hxpos.le]
    · have hx : x = 0 := le_antisymm (le_of_not_gt hxpos) (le_of_not_gt hx0)
      subst x
      rw [hasDerivAt_iff_tendsto_slope]
      have heq : (fun y : ℝ => slope q3PositiveCube 0 y) =ᶠ[nhdsWithin 0 ({0}ᶜ)]
          fun y => (max y 0) ^ 2 := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy0 : y ≠ 0 := hy
        by_cases h : 0 ≤ y
        · simp [slope, q3PositiveCube, max_eq_left h]; field_simp [hy0]
        · simp [slope, q3PositiveCube, max_eq_right (le_of_not_ge h)]
      have hcont : ContinuousAt (fun y : ℝ => (max y 0) ^ 2) 0 :=
        ((continuous_id.max continuous_const).continuousAt).pow 2
      simpa using (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm

/-- The explicit first derivative of the frozen q3 kernel. -/
noncomputable def q3KernelD1 (x : ℝ) : ℝ :=
  Real.sqrt (3003 / 1024) * (3 * (max (1 - 4 * x ^ 2) 0) ^ 2) * (-8 * x)

/-- The explicit second derivative of the frozen q3 kernel. -/
noncomputable def q3KernelD2 (x : ℝ) : ℝ :=
  Real.sqrt (3003 / 1024) *
    (6 * max (1 - 4 * x ^ 2) 0 * (-8 * x) ^ 2 +
      3 * (max (1 - 4 * x ^ 2) 0) ^ 2 * (-8))

/-- The third derivative, assigned its derivative fallback value at the two cutoffs. -/
noncomputable def q3KernelD3 (x : ℝ) : ℝ :=
  if |x| < 1 / 2 then
    Real.sqrt (3003 / 1024) * (1152 * x - 7680 * x ^ 3)
  else 0

private noncomputable def q3KernelD2Poly (x : ℝ) : ℝ :=
  Real.sqrt (3003 / 1024) * (-24 + 576 * x ^ 2 - 1920 * x ^ 4)

private theorem q3KernelD2_eq_zero_of_abs_ge {x : ℝ} (hx : 1 / 2 ≤ |x|) :
    q3KernelD2 x = 0 := by
  rw [q3KernelD2, max_eq_right (show 1 - 4 * x ^ 2 ≤ 0 by nlinarith [sq_abs x])]
  ring

private theorem q3KernelD2Poly_hasDerivAt (x : ℝ) :
    HasDerivAt q3KernelD2Poly
      (Real.sqrt (3003 / 1024) * (1152 * x - 7680 * x ^ 3)) x := by
  have hconst : HasDerivAt (fun _ : ℝ => (-24 : ℝ)) 0 x := hasDerivAt_const x (-24)
  have h2 := HasDerivAt.const_mul (576 : ℝ) (hasDerivAt_pow 2 x)
  have h4 := HasDerivAt.const_mul (-1920 : ℝ) (hasDerivAt_pow 4 x)
  have hpoly : HasDerivAt (fun y : ℝ => -24 + 576 * y ^ 2 - 1920 * y ^ 4)
      (1152 * x - 7680 * x ^ 3) x := by
    convert hconst.add h2 |>.add h4 using 1
    · ext y
      change -24 + 576 * y ^ 2 - 1920 * y ^ 4 =
        (-24 + 576 * y ^ 2) + -1920 * y ^ 4
      ring
    · norm_num [pow_succ]
      ring
  change HasDerivAt (fun y : ℝ => Real.sqrt (3003 / 1024) *
    (-24 + 576 * y ^ 2 - 1920 * y ^ 4)) _ _
  exact HasDerivAt.const_mul (Real.sqrt (3003 / 1024)) hpoly

private theorem q3Kernel_argument_continuous :
    Continuous (fun x : ℝ => 1 - 4 * x ^ 2) := by fun_prop

private theorem q3Kernel_argument_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - 4 * y ^ 2) (-8 * x) x := by
  have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x := hasDerivAt_const x 1
  have hscale := HasDerivAt.const_mul (-4 : ℝ) (hasDerivAt_pow 2 x)
  have hfun : (fun y : ℝ => 1 - 4 * y ^ 2) =
      (fun _ : ℝ => (1 : ℝ)) + fun y => -4 * y ^ 2 := by
    funext y
    change 1 - 4 * y ^ 2 = 1 + (-4 * y ^ 2)
    ring
  rw [hfun]
  convert hconst.add hscale using 1; ring

/-- The q3 kernel has the stated first derivative at every real point. -/
theorem q3Kernel_hasDerivAt (x : ℝ) : HasDerivAt q3Kernel (q3KernelD1 x) x := by
  have hrepr : q3Kernel = fun y => Real.sqrt (3003 / 1024) *
      q3PositiveCube (1 - 4 * y ^ 2) := by
    funext y
    rw [q3Kernel_eq_positive_part]
    rfl
  rw [hrepr]
  have hcomp := (q3PositiveCube_hasDerivAt (1 - 4 * x ^ 2)).comp x
    (q3Kernel_argument_hasDerivAt x)
  simpa [q3KernelD1, q3PositiveCube, mul_comm, mul_left_comm, mul_assoc] using
    (HasDerivAt.const_mul (Real.sqrt (3003 / 1024) : ℝ) hcomp)

private theorem q3KernelD1_hasDerivAt (x : ℝ) :
    HasDerivAt q3KernelD1 (q3KernelD2 x) x := by
  have ht := q3Kernel_argument_hasDerivAt x
  have hp := (q3PositiveSquare_hasDerivAt (1 - 4 * x ^ 2)).comp x ht
  have hl : HasDerivAt (fun y : ℝ => -8 * y) (-8) x := by
    have hfun : (fun y : ℝ => -8 * y) = fun y => (-8 : ℝ) * id y := by
      funext y
      simp [id]
    rw [hfun]
    simpa using HasDerivAt.const_mul (-8 : ℝ) (hasDerivAt_id x)
  have hmul := hp.mul hl
  have hscaled := HasDerivAt.const_mul (Real.sqrt (3003 / 1024) * 3 : ℝ) hmul
  have hfun : q3KernelD1 = fun y =>
      (Real.sqrt (3003 / 1024) * 3) *
        (q3PositiveSquare (1 - 4 * y ^ 2) * (-8 * y)) := by
    funext y
    simp [q3KernelD1, q3PositiveSquare, mul_comm, mul_left_comm, mul_assoc]
  rw [hfun]
  convert hscaled using 1
  · funext y
    simp [Function.comp_def, q3PositiveSquare, mul_comm, mul_left_comm, mul_assoc]
  · simp [q3KernelD2, q3PositiveSquare, mul_comm, mul_left_comm, mul_assoc]
    ring


/-- On the open support, the third derivative is the classical polynomial derivative. -/
theorem q3Kernel_third_derivative_inside {x : ℝ} (hx : |x| < 1 / 2) :
    iteratedDeriv 3 q3Kernel x = Real.sqrt (3003 / 1024) * (1152 * x - 7680 * x ^ 3) := by
  have hfirst : deriv q3Kernel = q3KernelD1 := by
    funext y
    exact (q3Kernel_hasDerivAt y).deriv
  have hsecond : deriv q3KernelD1 = q3KernelD2 := by
    funext y
    exact (q3KernelD1_hasDerivAt y).deriv
  have hiter : iteratedDeriv 3 q3Kernel x = deriv q3KernelD2 x := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ]
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
    rw [show (1 : ℕ) = 0 + 1 by norm_num, iteratedDeriv_succ]
    rw [iteratedDeriv_zero, hfirst, hsecond]
  have htpos : 0 < 1 - 4 * x ^ 2 := by
    have hx' := abs_lt.mp hx
    nlinarith
  have htcont := q3Kernel_argument_continuous.continuousAt (x := x)
  have hposEvent : ∀ᶠ y : ℝ in nhds x, 0 < 1 - 4 * y ^ 2 :=
    htcont.eventually_mem (isOpen_Ioi.mem_nhds htpos)
  have hlocal : q3KernelD2 =ᶠ[nhds x] q3KernelD2Poly := by
    filter_upwards [hposEvent] with y hy
    have hmax : max (1 - 4 * y ^ 2) 0 = 1 - 4 * y ^ 2 := max_eq_left hy.le
    simp [q3KernelD2, q3KernelD2Poly, hmax]
    ring
  have hD2 := (q3KernelD2Poly_hasDerivAt x).congr_of_eventuallyEq hlocal
  have hderiv : deriv q3KernelD2 x =
      Real.sqrt (3003 / 1024) * (1152 * x - 7680 * x ^ 3) := hD2.deriv
  rw [hiter, hderiv]

/-- Outside the support, the third derivative is zero. -/
theorem q3Kernel_third_derivative_outside {x : ℝ} (hx : 1 / 2 < |x|) :
    iteratedDeriv 3 q3Kernel x = 0 := by
  have hfirst : deriv q3Kernel = q3KernelD1 := by
    funext y
    exact (q3Kernel_hasDerivAt y).deriv
  have hsecond : deriv q3KernelD1 = q3KernelD2 := by
    funext y
    exact (q3KernelD1_hasDerivAt y).deriv
  have hiter : iteratedDeriv 3 q3Kernel x = deriv q3KernelD2 x := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ]
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
    rw [show (1 : ℕ) = 0 + 1 by norm_num, iteratedDeriv_succ]
    rw [iteratedDeriv_zero, hfirst, hsecond]
  have htneg : 1 - 4 * x ^ 2 < 0 := by nlinarith [sq_abs x]
  have htcont := q3Kernel_argument_continuous.continuousAt (x := x)
  have hnegEvent : ∀ᶠ y : ℝ in nhds x, 1 - 4 * y ^ 2 < 0 :=
    htcont.eventually_mem (isOpen_Iio.mem_nhds htneg)
  have hlocal : q3KernelD2 =ᶠ[nhds x] fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [hnegEvent] with y hy
    have hmax : max (1 - 4 * y ^ 2) 0 = 0 := max_eq_right hy.le
    simp [q3KernelD2, hmax]
  have hzero : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x := hasDerivAt_const x 0
  have hD2 := hzero.congr_of_eventuallyEq hlocal
  have hderiv : deriv q3KernelD2 x = 0 := hD2.deriv
  rw [hiter, hderiv]

private theorem q3KernelD2_deriv_at_right_cutoff :
    deriv q3KernelD2 (1 / 2 : ℝ) = 0 := by
  have hconst : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0
      (Set.Ioi (1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    (hasDerivAt_const (1 / 2 : ℝ) (0 : ℝ)).hasDerivWithinAt
  have hside : HasDerivWithinAt q3KernelD2 0
      (Set.Ioi (1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    apply hconst.congr
    · intro y hy
      have hypos : 0 ≤ y := le_trans (by norm_num) hy.le
      apply q3KernelD2_eq_zero_of_abs_ge
      rw [abs_of_nonneg hypos]
      exact hy.le
    · norm_num [q3KernelD2]
  exact hside.deriv_eq_zero (uniqueDiffWithinAt_Ioi (1 / 2 : ℝ))

private theorem q3KernelD2_deriv_at_left_cutoff :
    deriv q3KernelD2 (-(1 / 2 : ℝ)) = 0 := by
  have hconst : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0
      (Set.Iio (-(1 / 2 : ℝ))) (-(1 / 2 : ℝ)) :=
    (hasDerivAt_const (-(1 / 2 : ℝ)) (0 : ℝ)).hasDerivWithinAt
  have hside : HasDerivWithinAt q3KernelD2 0
      (Set.Iio (-(1 / 2 : ℝ))) (-(1 / 2 : ℝ)) := by
    apply hconst.congr
    · intro y hy
      have hyneg : y ≤ 0 := le_trans hy.le (by norm_num)
      have hybound : 1 / 2 ≤ |y| := by
        rw [abs_of_nonpos hyneg]
        have hy' : y < -(1 / 2 : ℝ) := hy
        linarith
      exact q3KernelD2_eq_zero_of_abs_ge hybound
    · norm_num [q3KernelD2]
  exact hside.deriv_eq_zero (uniqueDiffWithinAt_Iio (-(1 / 2 : ℝ)))

/-- The iterated third derivative takes the fallback value zero at both cutoffs. -/
theorem q3Kernel_third_derivative_cutoffs :
    iteratedDeriv 3 q3Kernel (-(1 / 2 : ℝ)) = 0 ∧ iteratedDeriv 3 q3Kernel (1 / 2) = 0 := by
  have hfirst : deriv q3Kernel = q3KernelD1 := by
    funext y
    exact (q3Kernel_hasDerivAt y).deriv
  have hsecond : deriv q3KernelD1 = q3KernelD2 := by
    funext y
    exact (q3KernelD1_hasDerivAt y).deriv
  have hiter (x : ℝ) : iteratedDeriv 3 q3Kernel x = deriv q3KernelD2 x := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ]
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ]
    rw [show (1 : ℕ) = 0 + 1 by norm_num, iteratedDeriv_succ]
    rw [iteratedDeriv_zero, hfirst, hsecond]
  exact ⟨by rw [hiter]; exact q3KernelD2_deriv_at_left_cutoff,
    by rw [hiter]; exact q3KernelD2_deriv_at_right_cutoff⟩

/-- The explicit piecewise formula for the third iterated derivative, including both cutoffs. -/
theorem q3Kernel_third_derivative_piecewise (x : ℝ) :
    iteratedDeriv 3 q3Kernel x = q3KernelD3 x := by
  change iteratedDeriv 3 q3Kernel x =
    if |x| < 1 / 2 then Real.sqrt (3003 / 1024) * (1152 * x - 7680 * x ^ 3) else 0
  split_ifs with hinside
  · exact q3Kernel_third_derivative_inside hinside
  · by_cases heq : |x| = 1 / 2
    · rcases le_total 0 x with hx | hx
      · have hval : x = 1 / 2 := by rw [abs_of_nonneg hx] at heq; linarith
        subst x
        exact q3Kernel_third_derivative_cutoffs.2
      · have hval : x = -(1 / 2 : ℝ) := by rw [abs_of_nonpos hx] at heq; linarith
        subst x
        exact q3Kernel_third_derivative_cutoffs.1
    · have hout : 1 / 2 < |x| := lt_of_le_of_ne (le_of_not_gt hinside) (Ne.symm heq)
      exact q3Kernel_third_derivative_outside hout

private theorem q3KernelD1_continuous : Continuous q3KernelD1 := by
  have ht : Continuous (fun x : ℝ => 1 - 4 * x ^ 2) := by fun_prop
  have hm : Continuous (fun x : ℝ => max (1 - 4 * x ^ 2) 0) := ht.max continuous_const
  change Continuous (fun x : ℝ => Real.sqrt (3003 / 1024) *
    (3 * (max (1 - 4 * x ^ 2) 0) ^ 2) * (-8 * x))
  fun_prop

private theorem q3KernelD2_continuous : Continuous q3KernelD2 := by
  have ht : Continuous (fun x : ℝ => 1 - 4 * x ^ 2) := by fun_prop
  have hm : Continuous (fun x : ℝ => max (1 - 4 * x ^ 2) 0) := ht.max continuous_const
  change Continuous (fun x : ℝ => Real.sqrt (3003 / 1024) *
    (6 * max (1 - 4 * x ^ 2) 0 * (-8 * x) ^ 2 +
      3 * (max (1 - 4 * x ^ 2) 0) ^ 2 * (-8)))
  fun_prop

/-- The frozen q3 kernel is twice continuously differentiable on the whole line. -/
theorem q3Kernel_contDiff_two : ContDiff ℝ 2 q3Kernel := by
  have hderiv : deriv q3Kernel = q3KernelD1 := by
    funext x
    exact (q3Kernel_hasDerivAt x).deriv
  have hderivD1 : deriv q3KernelD1 = q3KernelD2 := by
    funext x
    exact (q3KernelD1_hasDerivAt x).deriv
  have hD1 : ContDiff ℝ 1 q3KernelD1 := by
    have hindex : (1 : WithTop ℕ∞) = 0 + 1 := by norm_num
    rw [hindex, contDiff_succ_iff_deriv]
    refine ⟨fun x => (q3KernelD1_hasDerivAt x).differentiableAt, ?_, ?_⟩
    · intro htop
      norm_num at htop
    · rw [hderivD1, contDiff_zero]
      exact q3KernelD2_continuous
  have hindex : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [hindex, contDiff_succ_iff_deriv]
  refine ⟨fun x => (q3Kernel_hasDerivAt x).differentiableAt, ?_, ?_⟩
  · intro htop
    norm_num at htop
  · rw [hderiv]
    exact hD1

/-- The kernel and its first two derivatives vanish at both support endpoints. -/
theorem q3Kernel_cutoff_values :
    q3Kernel (-1 / 2) = 0 ∧ q3Kernel (1 / 2) = 0 ∧
      q3KernelD1 (-1 / 2) = 0 ∧ q3KernelD1 (1 / 2) = 0 ∧
      q3KernelD2 (-1 / 2) = 0 ∧ q3KernelD2 (1 / 2) = 0 := by
  norm_num [q3Kernel, q3KernelD1, q3KernelD2]

/-- The q3 kernel is continuous, including at the two cutoff points. -/
theorem q3Kernel_continuous : Continuous q3Kernel := by
  have hpoly : Continuous (fun x : ℝ => 1 - 4 * x ^ 2) := by fun_prop
  have hmax : Continuous (fun x : ℝ => max (1 - 4 * x ^ 2) 0) :=
    hpoly.max continuous_const
  have hrepr : q3Kernel = fun x => Real.sqrt (3003 / 1024) * max (1 - 4 * x ^ 2) 0 ^ 3 :=
    funext q3Kernel_eq_positive_part
  rw [hrepr]
  exact continuous_const.mul (hmax.pow 3)

/-- The q3 kernel vanishes at and beyond either cutoff endpoint. -/
theorem q3Kernel_eq_zero_of_abs_ge {x : ℝ} (hx : 1 / 2 ≤ |x|) :
    q3Kernel x = 0 := by
  have hpoly : 1 - 4 * x ^ 2 ≤ 0 := by nlinarith [sq_abs x]
  rw [q3Kernel_eq_positive_part, max_eq_right hpoly]
  norm_num

private noncomputable def q3NormPrimitivePoly : Polynomial ℝ :=
  Polynomial.X - Polynomial.C 2 * Polynomial.X ^ 3 + Polynomial.C 3 * Polynomial.X ^ 5 -
    Polynomial.C (20 / 7 : ℝ) * Polynomial.X ^ 7 +
    Polynomial.C (5 / 3 : ℝ) * Polynomial.X ^ 9 -
    Polynomial.C (6 / 11 : ℝ) * Polynomial.X ^ 11 +
    Polynomial.C (1 / 13 : ℝ) * Polynomial.X ^ 13

private noncomputable def q3NormPrimitive (x : ℝ) : ℝ :=
  Polynomial.eval x q3NormPrimitivePoly

private theorem q3NormPrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt q3NormPrimitive
      (1 - 6 * x ^ 2 + 15 * x ^ 4 - 20 * x ^ 6 + 15 * x ^ 8 - 6 * x ^ 10 + x ^ 12) x := by
  have h := Polynomial.hasDerivAt q3NormPrimitivePoly x
  convert h using 1
  · rfl
  · simp [q3NormPrimitivePoly, Polynomial.derivative_X]
    ring

private theorem q3NormPolynomial_integral :
    ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ 6 = 2048 / 3003 := by
  have hcont : Continuous (fun x : ℝ => (1 - x ^ 2) ^ 6) := by fun_prop
  calc
    ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ 6 = q3NormPrimitive 1 - q3NormPrimitive (-1) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        convert q3NormPrimitive_hasDerivAt x using 1; ring
      · exact hcont.intervalIntegrable (-1) 1
    _ = 2048 / 3003 := by
      norm_num [q3NormPrimitive, q3NormPrimitivePoly]

/-- The frozen q3 kernel has unit squared integral. -/
theorem q3Kernel_sq_integral : ∫ x, q3Kernel x ^ 2 = 1 := by
  let f : ℝ → ℝ := fun x => q3Kernel x ^ 2
  have hsupp : Function.support f ⊆ Set.Ioc (-1) 1 := by
    intro x hx
    have hqx : q3Kernel x ≠ 0 := by
      intro hzero
      apply hx
      simp [f, hzero]
    have habs : |x| ≤ 1 / 2 := by
      by_contra h
      exact hqx (q3Kernel_eq_zero_of_abs_ge (le_of_not_ge h))
    constructor <;> have := abs_le.mp habs <;> nlinarith
  have hfull : ∫ x, f x = ∫ x in (-1 : ℝ)..1, f x :=
    (intervalIntegral.integral_eq_integral_of_support_subset hsupp).symm
  have hcont : Continuous f := by
    dsimp [f]
    exact q3Kernel_continuous.pow 2
  have hleft : ∫ x in (-1 : ℝ)..(-(1 / 2 : ℝ)), f x = 0 := by
    calc
      ∫ x in (-1 : ℝ)..(-(1 / 2 : ℝ)), f x = ∫ _x in (-1 : ℝ)..(-(1 / 2 : ℝ)), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (by norm_num)] at hx
        dsimp [f]
        have hxneg : x ≤ 0 := le_trans hx.2 (by norm_num)
        have habs : 1 / 2 ≤ |x| := by
          rw [abs_of_nonpos hxneg]
          nlinarith [hx.2]
        simp [q3Kernel_eq_zero_of_abs_ge habs]
      _ = 0 := by simp
  have hright : ∫ x in (1 / 2 : ℝ)..1, f x = 0 := by
    calc
      ∫ x in (1 / 2 : ℝ)..1, f x = ∫ _x in (1 / 2 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (by norm_num)] at hx
        dsimp [f]
        have habs : 1 / 2 ≤ |x| := by
          rw [abs_of_nonneg (le_trans (by norm_num) hx.1)]
          nlinarith [hx.1]
        simp [q3Kernel_eq_zero_of_abs_ge habs]
      _ = 0 := by simp
  have hmid : ∫ x in (-(1 / 2 : ℝ))..(1 / 2), f x =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2),
        (Real.sqrt (3003 / 1024)) ^ 2 * (1 - 4 * x ^ 2) ^ 6 := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [f]
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have hpos : 0 ≤ 1 - 4 * x ^ 2 := by
      have hbound : -(1 / 2 : ℝ) ≤ x ∧ x ≤ 1 / 2 := by
        exact ⟨hx.1, hx.2⟩
      have hx' : |x| ≤ 1 / 2 := abs_le.mpr hbound
      have hprod : 0 ≤ (1 / 2 - |x|) * (1 / 2 + |x|) :=
        mul_nonneg (sub_nonneg.mpr hx') (by positivity)
      have hsquare : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      nlinarith
    rw [q3Kernel_eq_positive_part, max_eq_left hpos]
    ring
  have hjoin₁ :
      (∫ x in (-1 : ℝ)..(-(1 / 2 : ℝ)), f x) + ∫ x in (-(1 / 2 : ℝ))..1, f x =
        ∫ x in (-1 : ℝ)..1, f x := by
    exact intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (-1) (-(1 / 2 : ℝ)))
      (hcont.intervalIntegrable (-(1 / 2 : ℝ)) 1)
  have hjoin₂ :
      (∫ x in (-(1 / 2 : ℝ))..(1 / 2), f x) + ∫ x in (1 / 2)..1, f x =
        ∫ x in (-(1 / 2 : ℝ))..1, f x := by
    exact intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (-(1 / 2 : ℝ)) (1 / 2))
      (hcont.intervalIntegrable (1 / 2) 1)
  have hchange :
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), (1 - x ^ 2 * 4) ^ 6 =
        (1 / 2 : ℝ) * ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ 6 := by
    have h := intervalIntegral.integral_comp_mul_add
        (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (c := (2 : ℝ))
        (fun t : ℝ => (1 - t ^ 2) ^ 6) (by norm_num) 0
    norm_num [smul_eq_mul, mul_pow, mul_comm, mul_left_comm, mul_assoc] at h
    exact h
  have hchange' :
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), (1 - 4 * x ^ 2) ^ 6 =
        (1 / 2 : ℝ) * ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ 6 := by
    have hpoint : ∀ x : ℝ, (1 - 4 * x ^ 2) ^ 6 = (1 - x ^ 2 * 4) ^ 6 := by
      intro x
      congr 1
      ring
    have hcanon := intervalIntegral.integral_congr
      (f := fun x : ℝ => (1 - 4 * x ^ 2) ^ 6)
      (g := fun x : ℝ => (1 - x ^ 2 * 4) ^ 6)
      (a := -(1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (μ := volume)
      (fun x _ => hpoint x)
    exact hcanon.trans hchange
  have hpoly : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ 6 = 2048 / 3003 :=
    q3NormPolynomial_integral
  have hsqrt : (Real.sqrt (3003 / 1024 : ℝ)) ^ 2 = 3003 / 1024 :=
    Real.sq_sqrt (by norm_num)
  rw [hfull]
  rw [← hjoin₁, hleft, zero_add, ← hjoin₂, hright, add_zero, hmid]
  rw [intervalIntegral.integral_const_mul, hchange', hpoly]
  rw [hsqrt]
  norm_num

/-- The frozen kernel is supported in its defining interval. -/
theorem q3Kernel_hasCompactSupport : HasCompactSupport q3Kernel := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  change q3Kernel x ≠ 0 at hx
  have habs : |x| ≤ 1 / 2 := by
    by_contra h
    have hgt : (1 / 2 : ℝ) < |x| := lt_of_not_ge h
    have hnot : ¬ |x| ≤ 1 / 2 := not_le_of_gt hgt
    rw [q3Kernel, ite_eq_right hnot] at hx
    exact hx rfl
  exact abs_le.mp habs

/-- The q3 kernel is integrable on the real line. -/
theorem q3Kernel_integrable : Integrable q3Kernel :=
  q3Kernel_continuous.integrable_of_hasCompactSupport q3Kernel_hasCompactSupport

end ASDExplicitGamma.Model

end
