module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! The actual twentieth-moment endpoint bound controls the L20 seminorm
used by the frozen native returns. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory
open scoped ENNReal

/-- A bound on the twentieth power integral gives the corresponding
extended L20 seminorm bound, including the infinite-value cases. -/
theorem eLpNorm_le_of_twentieth_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (H : ℝ≥0∞)
    (hmoment : (∫⁻ ω, ‖f ω‖ₑ ^ (20 : ℝ) ∂μ) ≤ H ^ (20 : ℝ)) :
    eLpNorm f 20 μ ≤ H := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num) (by norm_num) hf]
  calc
    (∫⁻ ω, ‖f ω‖ₑ ^ (20 : ℝ) ∂μ) ^ (1 / 20 : ℝ) ≤
        (H ^ (20 : ℝ)) ^ (1 / 20 : ℝ) :=
      ENNReal.rpow_le_rpow hmoment (by norm_num)
    _ = H := by
      rw [← ENNReal.rpow_mul]
      norm_num

end ASDExplicitGamma.Native
