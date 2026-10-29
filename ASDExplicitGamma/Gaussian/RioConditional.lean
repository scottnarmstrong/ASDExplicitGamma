module

public import ASDExplicitGamma.Gaussian.RioMoment
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Conditional centering cancels the initial moment variation -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ASDExplicitGamma.Gaussian

/-- The first moment variation vanishes for every conditionally centered increment. -/
theorem rioMomentDerivative_zero {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℝ} (hp : 2 ≤ p) {S X : Ω → ℝ}
    (hSm : AEStronglyMeasurable[m] S μ)
    (hS : MemLp S (ENNReal.ofReal p) μ) (hX : MemLp X (ENNReal.ofReal p) μ)
    (hzero : μ[X | m] =ᵐ[μ] 0) : rioMomentDerivative μ p S X 0 = 0 := by
  let w : Ω → ℝ := fun ω => p * |S ω| ^ (p - 2) * S ω
  have hw : AEStronglyMeasurable[m] w μ :=
    (continuous_rio_power_derivative hp).comp_aestronglyMeasurable hSm
  have hprod : Integrable (fun ω => w ω * X ω) μ := rio_integrable_first_product hp hS hX
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith only [hp])
  have hx := hX.integrable hp1
  have hce := condExp_mul_of_aestronglyMeasurable_left hw hprod hx
  have he : ∫ ω, w ω * X ω ∂μ = 0 := by
    rw [← integral_condExp hm]
    apply integral_eq_zero_of_ae
    filter_upwards [hce, hzero] with ω hω hXω
    change μ[(fun ω => w ω * X ω) | m] ω = w ω * μ[X | m] ω at hω
    change μ[(fun ω => w ω * X ω) | m] ω = 0
    rw [hω, hXω, Pi.zero_apply, mul_zero]
  simpa only [rioMomentDerivative, zero_mul, add_zero, w] using he

end ASDExplicitGamma.Gaussian
