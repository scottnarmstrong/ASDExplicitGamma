module

public import ASDExplicitGamma.Inverse.StoppedDiameterEstimates
public import ASDExplicitGamma.Inverse.StoppedLocalizedBounds
public import ASDExplicitGamma.Inverse.StoppedLocalizedMeasurable

/-! Ordinary real diameter fields for the source Lp and Bernstein estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The ordinary real source diameter, with the standard ENNReal.toReal
convention on the already proved null set of unbounded components. -/
def realDiameterField {Ω : Type*} (B : PlanarMarks Ω) (x : BlockSite) (ω : Ω) : ℝ :=
  (diameterField B ω x).toReal

/-- The actual localized field is finite at every sample, so its real form
retains exactly its literal in-box component diameter. -/
def realLocalizedDiameterField {Ω : Type*} (B : PlanarMarks Ω) (M N : ℕ)
    (x : BlockSite) (ω : Ω) : ℝ := (localizedDiameterField B M N x ω).toReal

theorem real_diameter_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : PlanarMarks Ω) (hL : ∀ x, MeasurableSet (B.localMark x))
    (hP : ∀ n x, MeasurableSet (B.positiveMark n x)) (x : BlockSite) :
    Measurable (realDiameterField B x) :=
  (diameter_field_measurable B hL hP x).ennreal_toReal

theorem real_localized_diameter_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : PlanarMarks Ω) (hL : ∀ x, MeasurableSet (B.localMark x))
    (hP : ∀ n x, MeasurableSet (B.positiveMark n x)) (M N : ℕ) (x : BlockSite) :
    Measurable (realLocalizedDiameterField B M N x) :=
  (localized_diameter_field_measurable B hL hP M N x).ennreal_toReal

/-- Both exact source tail envelopes transfer to the ordinary random field. -/
theorem real_diameter_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hfloor : Real.exp (-6000) ≤ q) (x : BlockSite) (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t < realDiameterField B x ω} ≤ min (26*q) (200*Real.exp (-t/4)) := by
  have hsub : {ω | t < realDiameterField B x ω} ⊆
      {ω | ENNReal.ofReal t < diameterField B ω x} := by
    intro ω hω
    have hh := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mpr hω
    exact hh.trans_le ENNReal.ofReal_toReal_le
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans
    (diameter_field_tail μ B q hB hq0 hq hfloor x t)

/-- Real localized diameters preserve the source rare-moment monotonicity
simultaneously at all blocks, labels and inspection radii almost surely. -/
theorem real_localized_diameter_ae_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000) :
    ∀ᵐ ω ∂μ, ∀ M N x, realLocalizedDiameterField B M N x ω ≤ realDiameterField B x ω := by
  filter_upwards [diameter_field_ae_ne_top μ B q hB hq0 hq] with ω hω
  intro M N x
  exact ENNReal.toReal_mono (hω x) (localized_diameter_field_le B M N x ω)

theorem real_localized_diameter_bounds {Ω : Type*} (B : PlanarMarks Ω)
    (M N : ℕ) (x : BlockSite) (ω : Ω) :
    0 ≤ realLocalizedDiameterField B M N x ω ∧
      realLocalizedDiameterField B M N x ω ≤ ((2*N+1:ℕ):ℝ) := by
  refine ⟨ENNReal.toReal_nonneg,?_⟩
  have hh := ENNReal.toReal_mono (by finiteness : ((2*N+1:ℕ):ℝ≥0∞) ≠ ∞)
    (localized_diameter_field_le_box B M N x ω)
  simpa only [ENNReal.toReal_natCast] using! hh

end
end ASDExplicitGamma.Inverse
