module

public import ASDExplicitGamma.Native.HeatRemainderMixedHolder

/-! Common individual caps pass to the correlated spatial average. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

/-- A probability-weighted finite spatial average preserves every common
prime norm cap. No independence of descendants is used. -/
theorem heat_remainder_average_prime_cap
    {Ω I : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Finset I) (w : I → ℝ) (hw : ∀ i ∈ s,0 ≤ w i) (hw1 : ∑ i ∈ s,w i=1)
    (T : I → Ω → ℝ) (hT : ∀ i ∈ s,AEStronglyMeasurable (T i) μ)
    (p : ℝ) (hp : 1 ≤ p) (A : ℝ≥0∞) (hcap : ∀ i ∈ s,eLpNorm' (T i) p μ ≤ A) :
    eLpNorm' (fun ω => ∑ i ∈ s,w i*T i ω) p μ ≤ A := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hf (i : I) (hi : i ∈ s) : AEStronglyMeasurable (fun ω => w i*T i ω) μ :=
    (hT i hi).const_mul (w i)
  have hh := eLpNorm'_sum_le (f := fun i ω => w i*T i ω) hf hp
  have he (i : I) : eLpNorm' (fun ω => w i*T i ω) p μ = ‖w i‖ₑ*eLpNorm' (T i) p μ := by
    have hid : (fun ω => w i*T i ω)=w i • T i := by funext ω; rfl
    rw [hid,eLpNorm'_const_smul _ hp0]
  have hh' : eLpNorm' (fun ω => ∑ i ∈ s,w i*T i ω) p μ ≤ ∑ i ∈ s,‖w i‖ₑ*eLpNorm' (T i) p μ := by
    have hid : (∑ i ∈ s,fun ω => w i*T i ω) = (fun ω => ∑ i ∈ s,w i*T i ω) := by
      funext ω
      simp only [Finset.sum_apply]
    rw [hid] at hh
    simpa only [he] using hh
  apply hh'.trans
  calc
    ∑ i ∈ s,‖w i‖ₑ*eLpNorm' (T i) p μ ≤ ∑ i ∈ s,ENNReal.ofReal (w i)*A := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Real.enorm_eq_ofReal (hw i hi)]
      exact mul_le_mul' le_rfl (hcap i hi)
    _ = A := by rw [←Finset.sum_mul,←ENNReal.ofReal_sum_of_nonneg hw,hw1,ENNReal.ofReal_one,one_mul]

end
end ASDExplicitGamma.Native
