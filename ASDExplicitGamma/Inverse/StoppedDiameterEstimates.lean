module

public import ASDExplicitGamma.Inverse.StoppedDiameterTail
public import ASDExplicitGamma.Inverse.StoppedDiameterRarity
public import ASDExplicitGamma.Inverse.StoppedQ3Control

/-! The two source diameter tail envelopes, with their actual q3 instantiation. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Exact planar source tail min(26q,200 exp(-t/4)) for the literal Z field. -/
theorem diameter_field_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hfloor : Real.exp (-6000) ≤ q) (x : BlockSite) (t : ℝ) :
    μ.real {ω | ENNReal.ofReal t < diameterField B ω x} ≤ min (26*q) (200*Real.exp (-t/4)) := by
  apply le_min
  · have hsub : {ω | ENNReal.ofReal t < diameterField B ω x} ⊆
        {ω | 0 < diameterField B ω x} := fun _ hω => lt_of_le_of_lt (zero_le : (0:ℝ≥0∞) ≤ _) hω
    exact (measureReal_mono hsub (measure_ne_top μ _)).trans
      (diameter_field_rare_probability μ B q hB hfloor x)
  · exact diameter_field_exponential_tail μ B q hB hq0 hq x t

end
end ASDExplicitGamma.Inverse
