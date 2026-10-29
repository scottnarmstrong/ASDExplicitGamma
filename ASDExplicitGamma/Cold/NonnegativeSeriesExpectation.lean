module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # Expectation of a dominated nonnegative series -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace ASDExplicitGamma.Cold

/-- A summable deterministic envelope and one integrable random majorant justify
both series integrability and the expectation/series interchange. -/
theorem dominated_nonnegative_series_expectation {Ω : Type*} [MeasurableSpace Ω]
    {ℙ : Measure Ω} {F : ℕ → Ω → ℝ} {M : Ω → ℝ} {b : ℕ → ℝ}
    (hF : ∀ k, AEStronglyMeasurable (F k) ℙ) (hM : Integrable M ℙ)
    (_hb : ∀ k, 0 ≤ b k) (hbs : Summable b)
    (hFn : ∀ᵐ ω ∂ℙ, ∀ k, 0 ≤ F k ω)
    (hbound : ∀ᵐ ω ∂ℙ, ∀ k, F k ω ≤ b k*M ω) :
    Integrable (fun ω => ∑' k, F k ω) ℙ ∧
      Summable (fun k => ∫ ω, F k ω ∂ℙ) ∧
      (∫ ω, ∑' k, F k ω ∂ℙ) = ∑' k, ∫ ω, F k ω ∂ℙ := by
  have hsum : ∀ᵐ ω ∂ℙ, Summable (fun k => F k ω) := by
    filter_upwards [hFn,hbound] with ω hn hω
    exact Summable.of_nonneg_of_le hn hω (hbs.mul_right (M ω))
  have hfi (k : ℕ) : Integrable (F k) ℙ := by
    apply (hM.const_mul (b k)).mono' (hF k)
    filter_upwards [hFn,hbound] with ω hn hω
    rw [Real.norm_eq_abs,abs_of_nonneg (hn k)]
    exact hω k
  have hsi : Summable (fun k => ∫ ω, F k ω ∂ℙ) := by
    apply Summable.of_nonneg_of_le (fun k => integral_nonneg_of_ae (hFn.mono fun _ h => h k))
      (fun k => ?_) (hbs.mul_right (∫ ω, M ω ∂ℙ))
    have h := integral_mono_ae (hfi k) (hM.const_mul (b k)) (hbound.mono fun _ h => h k)
    rwa [integral_const_mul] at h
  have hseriesmeas : AEStronglyMeasurable (fun ω => ∑' k, F k ω) ℙ := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun N => (Finset.range N).aestronglyMeasurable_fun_sum (fun k _ => hF k))
    exact hsum.mono (fun _ h => h.hasSum.tendsto_sum_nat)
  have hseriesint : Integrable (fun ω => ∑' k, F k ω) ℙ := by
    apply (hM.const_mul (∑' k, b k)).mono' hseriesmeas
    filter_upwards [hFn,hbound,hsum] with ω hn hω hs
    rw [Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg hn)]
    have h := hs.tsum_le_tsum hω (hbs.mul_right (M ω))
    rwa [tsum_mul_right] at h
  refine ⟨hseriesint,hsi,?_⟩
  apply (integral_tsum_of_summable_integral_norm hfi ?_).symm
  convert hsi using 1
  funext k
  apply integral_congr_ae
  exact hFn.mono (fun ω h => by simp only [Real.norm_eq_abs,abs_of_nonneg (h k)])

end ASDExplicitGamma.Cold
