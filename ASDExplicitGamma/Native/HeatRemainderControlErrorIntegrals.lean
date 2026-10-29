module

public import ASDExplicitGamma.Native.HeatRemainderControlMixedProducts
public import ASDExplicitGamma.Native.HeatRemainderControlTraceProducts

/-! Every correlated term in the complete VHEAT error is retained. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

section Rare
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R A T : Ω → ℝ)
    (hR : AEStronglyMeasurable R μ) (hA : AEStronglyMeasurable A μ)
    (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ ω, 0 ≤ R ω) (hA0 : ∀ ω, 0 ≤ A ω) (hT0 : ∀ ω, 0 ≤ T ω)
    (ε X F : ℝ) (hε : 0 ≤ ε) (hX : 0 < X) (hF : 0 ≤ F)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hA20 : eLpNorm A 20 μ ≤ ENNReal.ofReal X)
    (hT20 : eLpNorm T 20 μ ≤ ENNReal.ofReal X)
    (hA128 : eLpNorm A 128 μ ≤ ENNReal.ofReal F)
    (hT128 : eLpNorm T 128 μ ≤ ENNReal.ofReal F)
include hR hA hT hR0 hA0 hT0 hε hX hF hR128 hA20 hT20 hA128 hT128

/-- The complete rare drift product, including its predecessor moment. -/
theorem nativeHeat_rare_linear_error_integral
    (j a : ℕ) (hj : j ≤ 2) (ha : a + 1 ≤ 20) :
    Integrable (fun ω => R ω ^ j * (A ω ^ a * (T ω + 4))) μ ∧
      (∫ ω, R ω ^ j * (A ω ^ a * (T ω + 4)) ∂μ) ≤
        4 * nativeHeatVHEATJ ε X F 20 j a + nativeHeatVHEATJ ε X F 20 j (a + 1) := by
  have h0 := nativeHeat_correlated_rare_mixed_product_le_J μ R A T hR hA hT hR0 hA0 hT0
    ε X F hε hX hF hR128 hA20 hT20 hA128 hT128 j a 0 hj (by omega)
  have h1 := nativeHeat_correlated_rare_mixed_product_le_J μ R A T hR hA hT hR0 hA0 hT0
    ε X F hε hX hF hR128 hA20 hT20 hA128 hT128 j a 1 hj ha
  have he : (fun ω => R ω ^ j * (A ω ^ a * (T ω + 4))) =
      (fun ω => 4 * (R ω ^ j * (A ω ^ a * T ω ^ 0)) + R ω ^ j * (A ω ^ a * T ω ^ 1)) := by
    funext ω
    ring
  have hi := (h0.1.const_mul 4).add h1.1
  refine ⟨he.symm ▸ hi, ?_⟩
  rw [he, integral_add (h0.1.const_mul 4) h1.1, integral_const_mul]
  simpa only [Nat.add_zero] using
    add_le_add (mul_le_mul_of_nonneg_left h0.2 (by norm_num : (0 : ℝ) ≤ 4)) h1.2

end Rare

/-- The bounded OLD-bank bracket keeps the separate heat-average envelope
Y. Neither T nor T+4 is removed from the actual integrand. -/
theorem nativeHeat_bounded_quadratic_error_integral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A T : Ω → ℝ) (hA : AEStronglyMeasurable A μ) (hT : AEStronglyMeasurable T μ)
    (hA0 : ∀ ω, 0 ≤ A ω) (hT0 : ∀ ω, 0 ≤ T ω)
    (Y X : ℝ) (hY : 0 ≤ Y) (hX : 0 ≤ X)
    (hA20 : eLpNorm A 20 μ ≤ ENNReal.ofReal Y)
    (hT20 : eLpNorm T 20 μ ≤ ENNReal.ofReal X)
    (a : ℕ) (ha : a + 2 ≤ 20) :
    Integrable (fun ω => A ω ^ a * (T ω * (T ω + 4))) μ ∧
      (∫ ω, A ω ^ a * (T ω * (T ω + 4)) ∂μ) ≤ Y ^ a * (4 * X + X ^ 2) := by
  have h1 := nativeHeat_trace_mixed_product μ A T hA hT hA0 hT0 Y X hY hX hA20 hT20 a 1 (by omega)
  have h2 := nativeHeat_trace_mixed_product μ A T hA hT hA0 hT0 Y X hY hX hA20 hT20 a 2 ha
  have he : (fun ω => A ω ^ a * (T ω * (T ω + 4))) =
      (fun ω => 4 * (A ω ^ a * T ω ^ 1) + A ω ^ a * T ω ^ 2) := by funext ω; ring
  have hi := (h1.1.const_mul 4).add h2.1
  refine ⟨he.symm ▸ hi, ?_⟩
  rw [he, integral_add (h1.1.const_mul 4) h2.1, integral_const_mul]
  have hb := add_le_add (mul_le_mul_of_nonneg_left h1.2 (by norm_num : (0 : ℝ) ≤ 4)) h2.2
  convert hb using 1 <;> ring

end
end ASDExplicitGamma.Native
