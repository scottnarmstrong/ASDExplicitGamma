module

public import ASDExplicitGamma.Gaussian.MappedHeat

/-! # Polynomial tests have all finite moments along mapped actual insertions -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

/-- Polynomial growth preserves all finite moments of a random field. -/
theorem memLp_polynomial {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (ρ : Measure Ω) [IsFiniteMeasure ρ] (Z : Ω → E) (hZ : Measurable Z)
    (hMom : ∀ p : ℝ, 2 ≤ p → MemLp Z (ENNReal.ofReal p) ρ)
    (Φ : E → ℝ) (hΦ : Measurable Φ) (hg : HasPolynomialGrowth Φ)
    {p : ℝ} (hp : 2 ≤ p) : MemLp (fun ω => Φ (Z ω)) (ENNReal.ofReal p) ρ := by
  obtain ⟨C, hC, d, hb⟩ := hg
  have hn : 0 < (d + 1 : ℝ) := by positivity
  have hre : 2 ≤ p * (d + 1 : ℝ) := by nlinarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
  have hnorm := (memLp_const (1 : ℝ) (μ := ρ) (p := ENNReal.ofReal (p * (d + 1 : ℝ)))).add (hMom _ hre).norm
  have hh := hnorm.norm_rpow_div (ENNReal.ofReal (d + 1 : ℝ))
  rw [← ENNReal.ofReal_div_of_pos hn, mul_div_cancel_right₀ _ hn.ne'] at hh
  have hpw : MemLp (fun ω => (1 + ‖Z ω‖) ^ (d + 1)) (ENNReal.ofReal p) ρ := by
    have he (ω : Ω) : ‖1 + ‖Z ω‖‖ = 1 + ‖Z ω‖ := Real.norm_of_nonneg (by positivity)
    simpa only [Pi.add_apply, ENNReal.toReal_ofReal hn.le, he,
      ← Real.rpow_natCast, Nat.cast_add, Nat.cast_one] using hh
  apply (hpw.const_smul C).mono' (hΦ.comp hZ).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => (hb (Z ω)).trans (by
    have hh := pow_le_pow_right₀ (by linarith [norm_nonneg (Z ω)] : 1 ≤ 1 + ‖Z ω‖)
      (show d ≤ d + 1 by omega)
    simpa only [Pi.smul_apply, smul_eq_mul] using mul_le_mul_of_nonneg_left hh hC)

end ASDExplicitGamma.Gaussian
