module

public import ASDExplicitGamma.Inverse.BankLpArithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The first-local order-128 cap pays the cubic signed-generator envelope. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory
open scoped ENNReal

theorem bank_cubic_integral_of_L128 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : Ω → ℝ) (hB : Measurable B)
    (hB0 : ∀ ω, 0 ≤ B ω) (b : ℝ) (hb : 0 ≤ b)
    (hcap : eLpNorm B 128 μ ≤ ENNReal.ofReal b) :
    Integrable (fun ω => B ω^3) μ ∧ (∫ ω, B ω^3 ∂μ) ≤ b^3 := by
  have h3 : eLpNorm B 3 μ ≤ ENNReal.ofReal b := by
    have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (f:=B) (μ:=μ)
      (p:=3) (q:=128) (by norm_num) hB.aestronglyMeasurable
    simp only [measure_univ,ENNReal.one_rpow,mul_one] at hh
    exact hh.trans hcap
  have heq : (eLpNorm B 3 μ)^3 = ∫⁻ ω, ENNReal.ofReal (B ω^3) ∂μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hB.aestronglyMeasurable]
    norm_num only [ENNReal.toReal_ofNat]
    simp_rw [Real.enorm_eq_ofReal (hB0 _),ENNReal.rpow_ofNat,
      ← ENNReal.ofReal_pow (hB0 _)]
    rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
    norm_num
  have hlin : (∫⁻ ω, ENNReal.ofReal (B ω^3) ∂μ) ≤ ENNReal.ofReal (b^3) := by
    rw [← heq,ENNReal.ofReal_pow hb]
    exact pow_le_pow_left' h3 3
  have hInt : Integrable (fun ω => B ω^3) μ := by
    refine ⟨(hB.pow_const 3).aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
    simp_rw [Real.enorm_eq_ofReal (pow_nonneg (hB0 _) 3)]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  refine ⟨hInt,?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => pow_nonneg (hB0 ω) 3)
    (hB.pow_const 3).aestronglyMeasurable]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
  rwa [ENNReal.toReal_ofReal (pow_nonneg hb 3)] at hh

/-- The pathwise signed generator and trace domination give the cubic envelope.
No independence between the response and its inverse history is used. -/
theorem bank_signed_generator_cubic {L v mu B d : ℝ}
    (hv : 0 ≤ v) (hmu : 0 ≤ mu)
    (hgen : L ≤ v*mu*B^2*d) (htrace : d ≤ 2*B) :
    L ≤ 2*v*mu*B^3 := by
  calc
    L ≤ v*mu*B^2*d := hgen
    _ ≤ v*mu*B^2*(2*B) := mul_le_mul_of_nonneg_left htrace
      (mul_nonneg (mul_nonneg hv hmu) (sq_nonneg B))
    _ = _ := by ring

end ASDExplicitGamma.Inverse
