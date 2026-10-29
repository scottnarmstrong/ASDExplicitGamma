module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory
open scoped ENNReal

/-- A nonnegative real twentieth-moment estimate gives the exact extended
L20 bound used by the frozen native observables. -/
theorem eLpNorm_twenty_le_of_integral_pow {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hpos : ∀ᵐ ω ∂μ, 0 ≤ f ω) (hi : Integrable (fun ω => f ω ^ 20) μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : (∫ ω, f ω ^ 20 ∂μ) ≤ C ^ 20) :
    eLpNorm f 20 μ ≤ ENNReal.ofReal C := by
  have he : (fun ω => ‖f ω‖ ^ ((20 : ℝ≥0∞).toReal)) =ᵐ[μ] (fun ω => f ω ^ 20) := by
    filter_upwards [hpos] with ω hω
    simp [Real.norm_eq_abs, abs_of_nonneg hω]
  have hmem : MemLp f 20 μ :=
    (integrable_norm_rpow_iff hf (by norm_num : (20 : ℝ≥0∞) ≠ 0)
      (by norm_num : (20 : ℝ≥0∞) ≠ ∞)).mp (hi.congr he.symm)
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num), integral_congr_ae he]
  apply ENNReal.ofReal_le_ofReal
  have hi0 : 0 ≤ ∫ ω, f ω ^ 20 ∂μ := integral_nonneg (fun ω => by positivity)
  have hr := (Real.rpow_inv_le_iff_of_pos hi0 hC (by norm_num : (0 : ℝ) < 20)).mpr
    (hb.trans_eq (Real.rpow_natCast C 20).symm)
  simpa using hr

end ASDExplicitGamma.Scalar
