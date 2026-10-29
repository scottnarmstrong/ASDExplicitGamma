module

public import ASDExplicitGamma.Inverse.StoppedRealDiameter
public import ASDExplicitGamma.Inverse.StoppedTailExponentialMoment

/-! A fixed shift turns the literal diameter tail into a unit exponential tail. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
noncomputable section

/-- Positive excess above 24; no truncation of the actual large diameters. -/
def diameterExcess {Ω : Type*} (B : PlanarMarks Ω) (x : BlockSite) (ω : Ω) : ℝ :=
  max (realDiameterField B x ω-24) 0

theorem diameter_excess_nonneg {Ω : Type*} (B : PlanarMarks Ω) (x : BlockSite) (ω : Ω) :
    0 ≤ diameterExcess B x ω := le_max_right _ _

theorem diameter_excess_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : PlanarMarks Ω) (hL : ∀ x, MeasurableSet (B.localMark x))
    (hP : ∀ n x, MeasurableSet (B.positiveMark n x)) (x : BlockSite) :
    Measurable (diameterExcess B x) :=
  ((real_diameter_measurable B hL hP x).sub_const 24).max measurable_const

/-- The fixed shift costs no source moment: 200 exp(-6)<=1. -/
theorem diameter_shift_cost : 200*Real.exp (-6) ≤ (1:ℝ) := by
  have h200 : (200:ℝ) ≤ Real.exp 6 := by
    have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 6) 7
    norm_num [Finset.sum_range_succ,Nat.factorial] at hh
    linarith only [hh]
  rw [Real.exp_neg,mul_inv_le_iff₀ (Real.exp_pos _)]
  simpa only [one_mul] using h200

theorem diameter_excess_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hfloor : Real.exp (-6000) ≤ q) (x : BlockSite) (t : ℝ) (ht : 0 < t) :
    μ.real {ω | t < diameterExcess B x ω} ≤ Real.exp (-t/4) := by
  have hsub : {ω | t < diameterExcess B x ω} ⊆ {ω | t+24 < realDiameterField B x ω} := by
    intro ω hω
    change t < max (realDiameterField B x ω-24) 0 at hω
    rcases lt_max_iff.mp hω with hω | hω
    · change t+24 < realDiameterField B x ω
      linarith only [hω]
    · exact False.elim (not_lt_of_ge ht.le hω)
  have hh := (real_diameter_tail μ B q hB hq0 hq hfloor x (t+24) (by linarith only [ht])).trans (min_le_right _ _)
  calc
    _ ≤ μ.real {ω | t+24 < realDiameterField B x ω} := measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ 200*Real.exp (-(t+24)/4) := hh
    _ = (200*Real.exp (-6))*Real.exp (-t/4) := by
      rw [show -(t+24)/4 = -6+(-t/4) by ring,Real.exp_add]
      ring
    _ ≤ _ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right diameter_shift_cost (Real.exp_pos (-t/4)).le

/-- The excess exponential moment and its integrability are both derived
from the actual source tail; neither is an additional model premise. -/
theorem diameter_excess_exp_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hfloor : Real.exp (-6000) ≤ q) (x : BlockSite) :
    Integrable (fun ω => Real.exp (diameterExcess B x ω/8)) μ ∧
      (∫ ω, Real.exp (diameterExcess B x ω/8) ∂μ) ≤ 2 :=
  exp_moment_of_unit_tail μ _
    (diameter_excess_measurable B hB.local_measurable hB.positive_measurable x)
    (diameter_excess_nonneg B x) (diameter_excess_tail μ B q hB hq0 hq hfloor x)

end
end ASDExplicitGamma.Inverse
