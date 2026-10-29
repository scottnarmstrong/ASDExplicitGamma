module

public import ASDExplicitGamma.Inverse.WeightedLocalizationColors
public import Mathlib.Probability.Moments.Variance

/-! Centering a bounded nonnegative field preserves its variance-sensitive source parameters. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization.IndependentSums MeasureTheory ProbabilityTheory

/-- A variable in [0,M] is integrable and its ordinary mean stays in that interval. -/
theorem localization_bounded_mean {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (X : Ω → ℝ) (hm : Measurable X)
    (M : ℝ) (_hM : 0 ≤ M) (hX : ∀ᵐ ω ∂mu, 0 ≤ X ω ∧ X ω ≤ M) :
    Integrable X mu ∧ 0 ≤ (∫ ω, X ω ∂mu) ∧ (∫ ω, X ω ∂mu) ≤ M := by
  have hb : ∀ᵐ ω ∂mu, |X ω| ≤ M := hX.mono (fun ω hω => by rw [abs_of_nonneg hω.1]; exact hω.2)
  have hi := integrable_of_abs_le_const hm.aemeasurable hb
  refine ⟨hi, integral_nonneg_of_ae (hX.mono (fun _ h => h.1)), ?_⟩
  calc
    _ ≤ ∫ _ω : Ω, M ∂mu := integral_mono_ae hi (integrable_const _) (hX.mono (fun _ h => h.2))
    _ = M := by simp

/-- Centering a [0,M] variable has absolute bound M, rather than 2M. -/
theorem localization_centered_abs_bound {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (X : Ω → ℝ) (hm : Measurable X)
    (M : ℝ) (hM : 0 ≤ M) (hX : ∀ᵐ ω ∂mu, 0 ≤ X ω ∧ X ω ≤ M) :
    ∀ᵐ ω ∂mu, |X ω - ∫ η, X η ∂mu| ≤ M := by
  obtain ⟨_, hlo, hhi⟩ := localization_bounded_mean mu X hm M hM hX
  filter_upwards [hX] with ω hω
  exact abs_le.mpr ⟨by linarith only [hω.1, hhi], by linarith only [hω.2, hlo]⟩

/-- Centering costs no second-moment factor; deterministic weights enter squared. -/
theorem localization_weighted_centered_moment {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (X : Ω → ℝ) (hm : Measurable X)
    (w v0 : ℝ) (hX2 : moment X 2 mu ≤ v0) :
    moment (fun ω => w * (X ω - ∫ η, X η ∂mu)) 2 mu ≤ w ^ 2 * v0 := by
  simp only [moment, Pi.pow_apply, mul_pow]
  rw [integral_const_mul, ← variance_eq_integral hm.aemeasurable]
  exact mul_le_mul_of_nonneg_left ((variance_le_expectation_sq hm.aestronglyMeasurable).trans hX2)
    (sq_nonneg w)

/-- The weighted centered variable has exactly zero ordinary expectation. -/
theorem localization_weighted_centered_mean {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (X : Ω → ℝ) (hi : Integrable X mu) (w : ℝ) :
    (∫ ω, w * (X ω - ∫ η, X η ∂mu) ∂mu) = 0 := by
  rw [integral_const_mul, integral_sub hi (integrable_const _)]
  simp

/-- The exact squared-weight sum retains the true layer mass. -/
theorem localization_weight_square_sum {ι : Type*} (s : Finset ι) (w : ι → ℝ) (W : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : ∀ i ∈ s, w i ≤ W) :
    (∑ i ∈ s, (w i) ^ 2) ≤ W * ∑ i ∈ s, w i := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i hi => by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right (hW i hi) (hw i hi))

end ASDExplicitGamma.Inverse
