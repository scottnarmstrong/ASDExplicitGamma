module

public import ASDExplicitGamma.Gaussian.TwoParameter
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-! # Hölder's inequality in the moment-generator estimate -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

/-- The real nonnegative Lᵖ norm, in the integral representation used for the moment estimates. -/
noncomputable def positiveLpNorm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ) (f : Ω → ℝ) : ℝ := (∫ ω, f ω ^ p ∂μ) ^ p⁻¹

/-- For nonnegative tests this is exactly the usual finite Lᵖ seminorm. -/
theorem positiveLpNorm_eq_eLpNorm_toReal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {p : ℝ} (hp : 0 < p) (f : Ω → ℝ) (hf0 : ∀ ω, 0 ≤ f ω)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    positiveLpNorm μ p f = (eLpNorm f (ENNReal.ofReal p) μ).toReal := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by positivity) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _)]
  simp only [positiveLpNorm, ENNReal.toReal_ofReal hp.le, Real.norm_of_nonneg (hf0 _)]

/-- The conjugate-exponent power used by Hölder. -/
theorem memLp_power_sub_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ} (hp : 1 < p) {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (fun ω => f ω ^ (p - 1)) (ENNReal.ofReal (p / (p - 1))) μ := by
  have hm : 0 < p - 1 := by linarith
  have hh := hf.norm_rpow_div (ENNReal.ofReal (p - 1))
  rw [← ENNReal.ofReal_div_of_pos hm] at hh
  simpa only [ENNReal.toReal_ofReal hm.le, Real.norm_of_nonneg (hf0 _)] using hh

/-- All products in the moment comparison are absolutely integrable. -/
theorem integrable_power_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ} (hp : 1 < p) {f g : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal p) μ) :
    Integrable (fun ω => f ω ^ (p - 1) * g ω) μ := by
  have hconj : (p / (p - 1)).HolderConjugate p :=
    (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl |>.symm
  let holderPowerProduct : ENNReal.HolderTriple (ENNReal.ofReal (p / (p - 1)))
      (ENNReal.ofReal p) 1 := hconj.ennrealOfReal
  exact (memLp_power_sub_one hp hf0 hf).integrable_mul hg

/-- The Hölder factor arising from differentiating a p-th moment, with all exponents real. -/
theorem integral_power_mul_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p : ℝ} (hp : 1 < p) {f g : Ω → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal p) μ) :
    ∫ ω, f ω ^ (p - 1) * g ω ∂μ ≤
      (∫ ω, f ω ^ p ∂μ) ^ (1 - p⁻¹) * positiveLpNorm μ p g := by
  have hconj : (p / (p - 1)).HolderConjugate p :=
    (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl |>.symm
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (ae_of_all μ fun ω => Real.rpow_nonneg (hf0 ω) _) (ae_of_all μ hg0)
    (memLp_power_sub_one hp hf0 hf) hg
  have he (ω : Ω) : (f ω ^ (p - 1)) ^ (p / (p - 1)) = f ω ^ p := by
    rw [← Real.rpow_mul (hf0 ω)]
    congr 1
    field_simp [show p - 1 ≠ 0 by linarith]
  simp only [he] at hh
  have heq : 1 / (p / (p - 1)) = 1 - p⁻¹ := by field_simp
  simpa only [heq, one_div, positiveLpNorm] using hh

end ASDExplicitGamma.Gaussian
