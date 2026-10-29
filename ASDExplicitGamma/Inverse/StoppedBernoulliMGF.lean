module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Ring

/-! Exact bounded event MGFs for independent marked-path subfamilies. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory ProbabilityTheory
noncomputable section

/-- The literal occupied-mark indicator. -/
def markIndicator {Ω : Type*} (E : Set Ω) : Ω → ℝ := E.indicator (fun _ => 1)

theorem mark_indicator_measurable {Ω : Type*} [MeasurableSpace Ω] (E : Set Ω)
    (hE : MeasurableSet E) : Measurable (markIndicator E) := measurable_const.indicator hE

theorem mark_indicator_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E) :
    Integrable (markIndicator E) μ := (integrable_const 1).indicator hE

/-- The event indicator retains the exact Bernoulli exponential identity. -/
theorem mark_indicator_exp {Ω : Type*} (E : Set Ω) (t : ℝ) (ω : Ω) :
    Real.exp (t*markIndicator E ω) = 1+(Real.exp t-1)*markIndicator E ω := by
  classical
  by_cases hω : ω ∈ E <;> simp [markIndicator,hω]

/-- The exact event MGF depends on its actual probability, without centering. -/
theorem mark_mgf_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E) (t : ℝ) :
    (∫ ω, Real.exp (t*markIndicator E ω) ∂μ) = 1+(Real.exp t-1)*μ.real E := by
  simp_rw [mark_indicator_exp]
  rw [integral_add (integrable_const 1)
    ((mark_indicator_integrable μ E hE).const_mul (Real.exp t-1)),integral_const_mul]
  have he : (∫ ω, markIndicator E ω ∂μ) = μ.real E := by
    simpa only [markIndicator,smul_eq_mul,mul_one] using integral_indicator_const (μ := μ) (1:ℝ) hE
  rw [he]
  simp [integral_const]

/-- The standard Bernoulli MGF cost at nonnegative tilt, using the supplied
actual event-probability upper bound. -/
theorem mark_mgf_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E)
    (q t : ℝ) (ht : 0 ≤ t) (hq : μ.real E ≤ q) :
    (∫ ω, Real.exp (t*markIndicator E ω) ∂μ) ≤ Real.exp (q*(Real.exp t-1)) := by
  rw [mark_mgf_eq μ E hE t]
  have he : 0 ≤ Real.exp t-1 := sub_nonneg.mpr (Real.one_le_exp ht)
  calc
    _ ≤ 1+(Real.exp t-1)*q := add_le_add le_rfl (mul_le_mul_of_nonneg_left hq he)
    _ = q*(Real.exp t-1)+1 := by ring
    _ ≤ _ := Real.add_one_le_exp _

end
end ASDExplicitGamma.Inverse
