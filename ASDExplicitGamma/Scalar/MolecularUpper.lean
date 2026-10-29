module

public import ASDExplicitGamma.Statements.ShellVarianceSum
public import Algsuperdiff.Section3.Disorder.Cstar
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Ingredients for the projected molecular upper bound

The c⋆ evaluation is an explicit input of the normalization helper. This
module does not assert SC-MOLECULAR-UPPER: the physical realization of the
stationary projection and its finite-cube comparison are still required.
-/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Algsuperdiff.Section3

/-- The elementary tangent inequality used for reciprocal Jensen. -/
theorem reciprocal_tangent {b y : ℝ} (hy : 0 < y) :
    2 * b - y ≤ b ^ 2 * y⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ hy]
  nlinarith only [sq_nonneg (b - y)]

/-- Reciprocal Jensen for a positive random variable bounded away from zero.
Only the original variable's integrability is assumed; integrability of its
reciprocal is proved from the positive lower bound. -/
theorem inv_integral_le_integral_inv {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} {a : ℝ}
    (ha : 0 < a) (hf : Integrable f μ) (hlower : ∀ᵐ omega ∂μ, a ≤ f omega) :
    (∫ omega, f omega ∂μ)⁻¹ ≤ ∫ omega, (f omega)⁻¹ ∂μ := by
  have hpos : ∀ᵐ omega ∂μ, 0 < f omega := hlower.mono fun _ h => ha.trans_le h
  have hInv : Integrable (fun omega => (f omega)⁻¹) μ := by
    refine (integrable_const a⁻¹).mono' hf.aestronglyMeasurable.inv₀ ?_
    filter_upwards [hlower, hpos] with omega hl hp
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
    exact (inv_le_inv₀ hp ha).mpr hl
  let b := ∫ omega, f omega ∂μ
  have hab : a ≤ b := by
    have h := integral_mono_ae (integrable_const a) hf hlower
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hb : 0 < b := ha.trans_le hab
  have htan : ∀ᵐ omega ∂μ, 2 * b - f omega ≤ b ^ 2 * (f omega)⁻¹ :=
    hpos.mono fun _ hp => reciprocal_tangent hp
  have h := integral_mono_ae ((integrable_const (2 * b)).sub hf)
    (hInv.const_mul (b ^ 2)) htan
  change (∫ x, (2 * b - f x) ∂μ) ≤ (∫ x, b ^ 2 * (f x)⁻¹ ∂μ) at h
  rw [integral_sub (integrable_const (2 * b)) hf, integral_const,
    probReal_univ, one_smul, integral_const_mul] at h
  have hbound : b ≤ b ^ 2 * ∫ omega, (f omega)⁻¹ ∂μ := by
    change 2 * b - b ≤ _ at h
    linarith only [h]
  calc
    b⁻¹ = b / b ^ 2 := by field_simp
    _ ≤ _ := (div_le_iff₀ (sq_pos_of_pos hb)).mpr (by
      simpa only [mul_comm] using hbound)

end ASDExplicitGamma.Scalar
