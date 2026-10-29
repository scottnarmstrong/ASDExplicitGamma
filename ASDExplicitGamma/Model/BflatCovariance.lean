module

public import ASDExplicitGamma.Numerics.Model.Q3Modes
public import ASDExplicitGamma.Model.Q3DerivativeSmooth
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Positivity of the q3 sine-minus-cosine covariance modes -/

@[expose] public section

namespace ASDExplicitGamma.Model

open MeasureTheory
open Set

private def q3TailPolynomial (u : ℝ) : ℝ :=
  5*u^5 + 30*u^4 + 72*u^3 + 82*u^2 + 36*u + 6

private theorem q3Cov_deriv_tail_factor {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    deriv ASDExplicitGamma.q3Cov u =
      -(13/5 : ℝ) * u * (1-u)^6 * q3TailPolynomial u := by
  have hd := q3Cov_iteratedDeriv_eq_rightPolynomial (n := 1) (by norm_num) hu0 hu1
  have hp :
      (((Polynomial.derivative^[1]) q3CovRightPolynomial).eval u) =
        -(13/5 : ℝ) * u * (1-u)^6 * q3TailPolynomial u := by
    norm_num [q3CovRightPolynomial, Polynomial.derivative_X_pow, q3TailPolynomial]
    ring
  simpa only [iteratedDeriv_one, hp] using hd

private theorem q3Cov_deriv_nonpos_unit {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    deriv ASDExplicitGamma.q3Cov u ≤ 0 := by
  rw [q3Cov_deriv_tail_factor hu0 hu1]
  have hpoly : 0 ≤ q3TailPolynomial u := by
    unfold q3TailPolynomial
    positivity
  have hone : 0 ≤ 1-u := sub_nonneg.mpr hu1
  have hfactor : 0 ≤ (13/5 : ℝ) * u * (1-u)^6 * q3TailPolynomial u := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hu0)
      (pow_nonneg hone 6)) hpoly
  rw [show -(13/5 : ℝ) * u * (1-u)^6 * q3TailPolynomial u =
    -((13/5 : ℝ) * u * (1-u)^6 * q3TailPolynomial u) by ring]
  exact neg_nonpos.mpr hfactor

private theorem interval_integral_q3_cov_sine_nonneg (freq : ℝ) (hfreq : 0 < freq) :
    0 ≤ ∫ u in (0 : ℝ)..1, ASDExplicitGamma.q3Cov u * Real.sin (freq*u) := by
  let f : ℝ → ℝ := ASDExplicitGamma.q3Cov
  let g : ℝ → ℝ := fun u => -Real.cos (freq*u)/freq
  have hfcont : ContinuousOn f (Set.uIcc (0 : ℝ) 1) :=
    ASDExplicitGamma.Model.q3Cov_contDiff_two.continuous.continuousOn
  have hgcont : ContinuousOn g (Set.uIcc (0 : ℝ) 1) := by
    fun_prop
  have hfd : ∀ u ∈ Set.Ioo (min (0 : ℝ) 1) (max 0 1),
      HasDerivAt f (deriv f u) u := by
    intro u hu
    exact (ASDExplicitGamma.Model.q3Cov_contDiff_two.differentiable (by norm_num) u).hasDerivAt
  have hgd : ∀ u ∈ Set.Ioo (min (0 : ℝ) 1) (max 0 1),
      HasDerivAt g (Real.sin (freq*u)) u := by
    intro u hu
    have hid : HasDerivAt (fun x : ℝ => freq*x) freq u := by
      simpa using (hasDerivAt_id u).const_mul freq
    have hc : HasDerivAt (fun x : ℝ => Real.cos (freq*x))
        (-Real.sin (freq*u)*freq) u := by
      exact (Real.hasDerivAt_cos (freq*u)).comp u hid
    have hh := hc.const_mul (-freq⁻¹)
    have hfun : (fun x : ℝ => -Real.cos (freq*x)/freq) =
        (fun x => (-freq⁻¹)*Real.cos (freq*x)) := by
      funext x
      field_simp [ne_of_gt hfreq]
    have hderiv : (-freq⁻¹)*(-Real.sin (freq*u)*freq) = Real.sin (freq*u) := by
      field_simp [ne_of_gt hfreq]
    change HasDerivAt (fun x : ℝ => -Real.cos (freq*x)/freq)
      (Real.sin (freq*u)) u
    rw [hfun]
    exact hh.congr_deriv hderiv
  have hf' : IntervalIntegrable (deriv f) volume 0 1 := by
    exact (ASDExplicitGamma.Model.q3Cov_contDiff_two.continuous_deriv (by norm_num)).intervalIntegrable 0 1
  have hg' : IntervalIntegrable (fun u => Real.sin (freq*u)) volume 0 1 := by
    exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hfcont hgcont hfd hgd hf' hg'
  have hfund : ∫ u in (0 : ℝ)..1, deriv f u = f 1 - f 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => (ASDExplicitGamma.Model.q3Cov_contDiff_two.differentiable (by norm_num) u).hasDerivAt)
      (ASDExplicitGamma.Model.q3Cov_contDiff_two.continuous_deriv (by norm_num) |>.intervalIntegrable 0 1)
  have hf0 : f 0 = 1 := by simpa [f] using q3Cov_at_zero
  have hf1 : f 1 = 0 := by
    simpa [f] using q3Cov_zero_of_abs_ge_one
      (by norm_num : (1 : ℝ) ≤ |(1 : ℝ)|)
  have hcosint :
      (∫ u in (0 : ℝ)..1, deriv f u * Real.cos (freq*u)) =
        (∫ u in (0 : ℝ)..1, deriv f u * (Real.cos (freq*u)-1)) +
          (∫ u in (0 : ℝ)..1, deriv f u) := by
    have hcosCont : Continuous (fun u : ℝ => Real.cos (freq*u)) :=
      Real.continuous_cos.comp (continuous_const.mul continuous_id)
    have hi1 : IntervalIntegrable (fun u : ℝ => deriv f u * Real.cos (freq*u)) volume 0 1 :=
      hf'.mul_continuousOn hcosCont.continuousOn
    have hi2 : IntervalIntegrable (fun u : ℝ => deriv f u * (Real.cos (freq*u)-1)) volume 0 1 :=
      hf'.mul_continuousOn (hcosCont.sub continuous_const).continuousOn
    calc
      _ = ∫ u in (0 : ℝ)..1,
          (deriv f u * (Real.cos (freq*u)-1) + deriv f u) := by
            apply intervalIntegral.integral_congr
            intro u hu
            ring
      _ = _ := intervalIntegral.integral_add hi2 hf'
  have hformula :
      (∫ u in (0 : ℝ)..1, f u * Real.sin (freq*u)) =
        (∫ u in (0 : ℝ)..1, (-deriv f u) * (1-Real.cos (freq*u))) / freq := by
    have hfreq' : freq ≠ 0 := ne_of_gt hfreq
    rw [hibp]
    rw [hf0, hf1]
    simp only [zero_mul, one_mul, zero_sub]
    simp only [g, mul_zero, Real.cos_zero, neg_neg, neg_div]
    have hmul :
        (∫ u in (0 : ℝ)..1, deriv f u * (-(Real.cos (freq*u) / freq))) =
          (-1/freq) * (∫ u in (0 : ℝ)..1, deriv f u * Real.cos (freq*u)) := by
      rw [show (fun u : ℝ => deriv f u * (-(Real.cos (freq*u) / freq))) =
        (fun u => (-1/freq) * (deriv f u * Real.cos (freq*u))) by funext u; ring,
        intervalIntegral.integral_const_mul]
    have hintegral :
        (∫ u in (0 : ℝ)..1, deriv f u * (Real.cos (freq*u)-1)) =
          ∫ u in (0 : ℝ)..1, (-deriv f u) * (1-Real.cos (freq*u)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      ring
    rw [hmul, hcosint, hfund, hf1, hf0, ← hintegral]
    field_simp [hfreq']
    ring
  rw [hformula]
  apply div_nonneg
  · apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    have hderiv : deriv f u ≤ 0 := by
      simpa [f] using q3Cov_deriv_nonpos_unit hu.1 hu.2
    have hcos : Real.cos (freq*u) ≤ 1 := Real.cos_le_one _
    exact mul_nonneg (neg_nonneg.mpr hderiv) (sub_nonneg.mpr hcos)
  · exact le_of_lt hfreq

/-- The defect in the normalized sine and cosine covariance modes is nonnegative. -/
theorem q3ModeDifference_nonneg (j n : ℕ) : 0 ≤
    ASDExplicitGamma.Numerics.Model.q3ModeDifference j n := by
  let ell : ℝ := (ASDExplicitGamma.Numerics.Model.q3ModeLength j : ℚ)
  let m : ℝ := ((n+1 : ℕ) : ℝ)
  let freq : ℝ := Real.pi*m*ell
  have hell : 0 < ell := by
    dsimp [ell, ASDExplicitGamma.Numerics.Model.q3ModeLength]
    positivity
  have hm : 0 < m := by dsimp [m]; positivity
  have hfreq : 0 < freq := by dsimp [freq]; positivity
  have hmode :
      ASDExplicitGamma.Numerics.Model.q3ModeDifference j n =
        (4*ell/(Real.pi*m)) *
          (∫ u in (0 : ℝ)..1, ASDExplicitGamma.q3Cov u * Real.sin (freq*u)) := by
    unfold ASDExplicitGamma.Numerics.Model.q3ModeDifference
      ASDExplicitGamma.Numerics.Model.q3ModeSine
      ASDExplicitGamma.Numerics.Model.q3ModeCosine
      ASDExplicitGamma.Numerics.Model.q3SineCoefficient
      ASDExplicitGamma.Numerics.Model.q3ModeLength
      ASDExplicitGamma.Numerics.Model.q3ModeFrequency
    dsimp [ell, m, freq]
    norm_num [ASDExplicitGamma.Numerics.Model.q3ModeLength]
    ring
  rw [hmode]
  apply mul_nonneg
  · positivity
  · exact interval_integral_q3_cov_sine_nonneg freq hfreq

/-- The one-dimensional constant-mode covariance of the scaled q3 kernel. -/
theorem q3Cov_flat_constant_mode (ell : ℝ) :
    2*ell*(∫ u in (0 : ℝ)..1, ASDExplicitGamma.q3Cov u*(1-ell*u)) =
      (429/700 : ℝ)*ell-(7/60 : ℝ)*ell^2 := by
  have hrewrite :
      (∫ u in (0 : ℝ)..1, ASDExplicitGamma.q3Cov u*(1-ell*u)) =
        ∫ u in (0 : ℝ)..1,
          (1-ell*u-(39/5 : ℝ)*u^2+(39/5*ell)*u^3+(143/5 : ℝ)*u^4-
            (143/5*ell)*u^5-(429/5 : ℝ)*u^6+(429/5*ell)*u^7+
            (429/5 : ℝ)*u^7-(429/5*ell)*u^8-(143/5 : ℝ)*u^9+
            (143/5*ell)*u^10+(39/5 : ℝ)*u^11-(39/5*ell)*u^12-
            u^13+ell*u^14) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    change ASDExplicitGamma.q3Cov u*(1-ell*u) = _
    rw [q3Cov_eq_rightPolynomial hu.1 hu.2]
    simp only [q3CovRightPolynomial, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one]
    ring
  rw [hrewrite]
  repeat'
    first
    | (rw [intervalIntegral.integral_add] <;>
        all_goals try (apply Continuous.intervalIntegrable; fun_prop))
    | (rw [intervalIntegral.integral_sub] <;>
        all_goals try (apply Continuous.intervalIntegrable; fun_prop))
  repeat' (first | rw [intervalIntegral.integral_const_mul] |
    rw [intervalIntegral.integral_mul_const])
  repeat' (first | rw [intervalIntegral.integral_const] | rw [integral_id] |
    rw [integral_pow])
  norm_num
  ring

end ASDExplicitGamma.Model
