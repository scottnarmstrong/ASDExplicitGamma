/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Finite-dimensional Gaussian calculus

Integration by parts and the heat identity for finite-dimensional standard Gaussian vectors.
-/

@[expose] public section

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal NNReal

namespace ASDExplicitGamma.Gaussian

/-- A real-valued function has polynomial growth if it is bounded by a constant times an
integer power of one plus the norm. -/
def HasPolynomialGrowth {E : Type*} [NormedAddCommGroup E] (f : E → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ x, |f x| ≤ C * (1 + ‖x‖) ^ d

/-- A continuously differentiable function and its derivative obey one common polynomial bound. -/
def HasPolynomiallyBoundedDerivative (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ,
    ∀ x, |f x| + |deriv f x| ≤ C * (1 + |x|) ^ d

/-- Every exponential of the absolute value is integrable under a standard Gaussian. -/
lemma integrable_exp_abs_gaussianReal (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp (a * |x|)) (gaussianReal 0 1) := by
  refine Integrable.mono' ((integrable_exp_mul_gaussianReal a).add
    (integrable_exp_mul_gaussianReal (-a))) (by fun_prop) ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    change Real.exp (a * x) ≤ Real.exp (a * x) + Real.exp (-a * x)
    exact le_add_of_nonneg_right (Real.exp_pos (-a * x)).le
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx']
    change Real.exp (a * -x) ≤ Real.exp (a * x) + Real.exp (-a * x)
    rw [show a * -x = -a * x by ring]
    exact le_add_of_nonneg_left (Real.exp_pos (a * x)).le

/-- Polynomial growth implies Gaussian integrability. -/
private lemma integrable_of_polynomial_bound {f : ℝ → ℝ} {C : ℝ} {d : ℕ}
    (hf : Measurable f) (hC : 0 ≤ C)
    (hg : ∀ x, |f x| ≤ C * (1 + |x|) ^ d) :
    Integrable f (gaussianReal 0 1) := by
  have hmajor : Integrable (fun x : ℝ => C * Real.exp ((d : ℝ) * |x|))
      (gaussianReal 0 1) := by
    simpa only [smul_eq_mul] using
      (integrable_exp_abs_gaussianReal (d : ℝ)).const_mul C
  refine Integrable.mono' hmajor hf.aestronglyMeasurable ?_
  filter_upwards with x
  calc
    |f x| ≤ C * (1 + |x|) ^ d := hg x
    _ ≤ C * Real.exp ((d : ℝ) * |x|) := by
      apply mul_le_mul_of_nonneg_left _ hC
      calc
        (1 + |x|) ^ d ≤ (Real.exp |x|) ^ d := by
          gcongr
          simpa [add_comm] using Real.add_one_le_exp |x|
        _ = Real.exp ((d : ℝ) * |x|) := by rw [← Real.exp_nat_mul]

/-- Integrability against the standard Gaussian is equivalent to integrability of the density
weighted function against Lebesgue measure. -/
private lemma integrable_gaussianReal_std_iff {f : ℝ → ℝ} :
    Integrable f (gaussianReal 0 1) ↔
      Integrable (fun x => gaussianPDFReal 0 1 x * f x) volume := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (ae_of_all _ fun x => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul]

/-- A polynomial bound gives a Lebesgue-integrable Gaussian density multiple. -/
private lemma integrable_gaussianPDFReal_mul_of_polynomial_bound {f : ℝ → ℝ} {C : ℝ} {d : ℕ}
    (hf : Measurable f) (hC : 0 ≤ C)
    (hg : ∀ x, |f x| ≤ C * (1 + |x|) ^ d) :
    Integrable (fun x => gaussianPDFReal 0 1 x * f x) volume := by
  exact integrable_gaussianReal_std_iff.mp
    (integrable_of_polynomial_bound hf hC hg)

/-- Derivative of the standard Gaussian density. -/
private lemma hasDerivAt_gaussianPDFReal_std (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  rw [gaussianPDFReal_def]
  have hg : HasDerivAt (fun y : ℝ => (- (1 / 2 : ℝ)) * y ^ 2) (-x) x := by
    convert ((hasDerivAt_id x).pow 2).const_mul (-(1 / 2 : ℝ)) using 1 <;> simp
  have he := (Real.hasDerivAt_exp ((-(1 / 2 : ℝ)) * x ^ 2)).comp x hg
  have hp := he.const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
  convert hp using 1
  · funext y
    simp only [Function.comp_apply]
    congr 1
    · norm_num
    · apply congrArg Real.exp
      norm_num
      ring
  · dsimp
    norm_num only [NNReal.coe_one]
    have hcoeff : (Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ =
        (Real.sqrt (2 * Real.pi))⁻¹ := by norm_num
    rw [hcoeff]
    simp only [sub_zero]
    rw [show -(x ^ 2) / 2 = -(1 / 2 * x ^ 2) by ring]
    ring_nf

/-- Gaussian integration by parts on `ℝ`. -/
theorem integral_id_mul_eq_integral_deriv_gaussianReal
    {f : ℝ → ℝ} (hf : HasPolynomiallyBoundedDerivative f) :
    ∫ x, x * f x ∂(gaussianReal 0 1) = ∫ x, deriv f x ∂(gaussianReal 0 1) := by
  rcases hf.2 with ⟨C, hC, d, hbound⟩
  have hf_bound : ∀ x, |f x| ≤ C * (1 + |x|) ^ d := by
    intro x
    calc
      |f x| ≤ |f x| + |deriv f x| := le_add_of_nonneg_right (abs_nonneg _)
      _ ≤ C * (1 + |x|) ^ d := hbound x
  have hdf_bound : ∀ x, |deriv f x| ≤ C * (1 + |x|) ^ d := by
    intro x
    calc
      |deriv f x| ≤ |f x| + |deriv f x| := le_add_of_nonneg_left (abs_nonneg _)
      _ ≤ C * (1 + |x|) ^ d := hbound x
  have hxf_bound : ∀ x, |x * f x| ≤ C * (1 + |x|) ^ (d + 1) := by
    intro x
    calc
      |x * f x| = |x| * |f x| := abs_mul _ _
      _ ≤ (1 + |x|) * (C * (1 + |x|) ^ d) := by
        gcongr
        linarith [abs_nonneg x]
        exact hf_bound x
      _ = C * (1 + |x|) ^ (d + 1) := by rw [pow_succ]; ring
  have hfmeas : Measurable f := hf.1.continuous.measurable
  have hdfmeas : Measurable (deriv f) := hf.1.continuous_deriv_one.measurable
  have hxfmeas : Measurable (fun x => x * f x) := measurable_id'.mul hfmeas
  have hfv := integrable_gaussianPDFReal_mul_of_polynomial_bound hfmeas hC hf_bound
  have hdfv := integrable_gaussianPDFReal_mul_of_polynomial_bound hdfmeas hC hdf_bound
  have hxfv := integrable_gaussianPDFReal_mul_of_polynomial_bound hxfmeas hC hxf_bound
  have hu_v : Integrable (fun x => f x * gaussianPDFReal 0 1 x) volume := by
    convert hfv using 1
    ext x
    ring
  have hu'_v : Integrable (fun x => deriv f x * gaussianPDFReal 0 1 x) volume := by
    convert hdfv using 1
    ext x
    ring
  have hu_v' : Integrable (fun x => f x * (-x * gaussianPDFReal 0 1 x)) volume := by
    have hneg : Integrable (fun x => -(gaussianPDFReal 0 1 x * (x * f x))) volume := hxfv.neg
    exact hneg.congr (ae_of_all _ fun x => by ring)
  have hfd : ∀ x, HasDerivAt f (deriv f x) x := by
    intro x
    exact hasDerivAt_deriv_iff.mpr (hf.1.differentiable_one x)
  have hparts :
      ∫ x, f x * (-x * gaussianPDFReal 0 1 x) =
        -∫ x, deriv f x * gaussianPDFReal 0 1 x := by
    apply integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => hfd x) (fun x _ => hasDerivAt_gaussianPDFReal_std x)
      hu_v' hu'_v hu_v
  have hweighted :
      ∫ x, gaussianPDFReal 0 1 x * (x * f x) =
        ∫ x, gaussianPDFReal 0 1 x * deriv f x := by
    calc
      ∫ x, gaussianPDFReal 0 1 x * (x * f x)
          = ∫ x, -(f x * (-x * gaussianPDFReal 0 1 x)) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = -∫ x, f x * (-x * gaussianPDFReal 0 1 x) := by rw [integral_neg]
      _ = ∫ x, deriv f x * gaussianPDFReal 0 1 x := by rw [hparts]; simp
      _ = ∫ x, gaussianPDFReal 0 1 x * deriv f x := by
        apply integral_congr_ae
        filter_upwards with x
        ring
  have hleft :
      ∫ x, x * f x ∂(gaussianReal 0 1) =
        ∫ x, gaussianPDFReal 0 1 x * (x * f x) := by
    rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (f := fun x => x * f x)
      (by norm_num)]
    simp only [smul_eq_mul]
  have hright :
      ∫ x, deriv f x ∂(gaussianReal 0 1) =
        ∫ x, gaussianPDFReal 0 1 x * deriv f x := by
    rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (f := deriv f)
      (by norm_num)]
    simp only [smul_eq_mul]
  exact hleft.trans (hweighted.trans hright.symm)

end ASDExplicitGamma.Gaussian
