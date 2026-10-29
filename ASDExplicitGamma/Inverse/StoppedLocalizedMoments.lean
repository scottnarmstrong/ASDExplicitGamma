module

public import ASDExplicitGamma.Inverse.StoppedDiameterMomentCaps
public import ASDExplicitGamma.Inverse.WeightedLocalizationPartialBlocks

/-! The rare second moments in Bernstein are inherited from the actual full Z field. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory ProbabilityTheory
noncomputable section

/-- Every localized power is bounded and integrable in the actual probability
space, using its actual finite in-box diameter. -/
theorem localized_diameter_power_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω)
    (hL : ∀ x, MeasurableSet (B.localMark x)) (hP : ∀ n x, MeasurableSet (B.positiveMark n x))
    (M N : ℕ) (x : BlockSite) (m : ℕ) :
    Integrable (fun ω => (realLocalizedDiameterField B M N x ω)^m) μ := by
  have hm := (real_localized_diameter_measurable B hL hP M N x).pow_const m
  apply (integrable_const (((2*N+1:ℕ):ℝ)^m)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  obtain ⟨h0,h1⟩ := real_localized_diameter_bounds B M N x ω
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg h0 m)]
  exact pow_le_pow_left₀ h0 h1 m

/-- Pointwise monotone localization pays the full field's rare second moment,
so Bernstein does not replace it by the much larger bound (4N)^(2m). -/
theorem localized_power_second_moment_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (M N : ℕ) (x : BlockSite) (m : ℕ)
    (hi : Integrable (fun ω => (realDiameterField B x ω)^(2*m)) μ) :
    moment (fun ω => (realLocalizedDiameterField B M N x ω)^m) 2 μ ≤
      ∫ ω, (realDiameterField B x ω)^(2*m) ∂μ := by
  have hl := localized_diameter_power_integrable μ B hB.local_measurable hB.positive_measurable M N x (2*m)
  have hh : (∫ ω, (realLocalizedDiameterField B M N x ω)^(2*m) ∂μ) ≤
      ∫ ω, (realDiameterField B x ω)^(2*m) ∂μ := by
    apply integral_mono_ae hl hi
    filter_upwards [real_localized_diameter_ae_le μ B q hB hq0 hq] with ω hω
    exact pow_le_pow_left₀ (real_localized_diameter_bounds B M N x ω).1 (hω M N x) (2*m)
  simpa only [moment,Pi.pow_apply,pow_mul,Nat.mul_comm] using! hh

/-- Both source rare variance caps used in the planar Bernstein application. -/
theorem localized_rare_second_moment_caps {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hfloor : Real.exp (-6000) ≤ q) (M N : ℕ) (x : BlockSite) :
    moment (fun ω => (realLocalizedDiameterField B M N x ω)^2) 2 μ < 8 ∧
    moment (fun ω => (realLocalizedDiameterField B M N x ω)^4) 2 μ < 1000000000 := by
  obtain ⟨hi4,hi8,h4,h8⟩ := real_diameter_uniform_moments μ B q hB hq0 hq hfloor x
  exact ⟨(localized_power_second_moment_le μ B q hB hq0 hq M N x 2 hi4).trans_lt h4,
    (localized_power_second_moment_le μ B q hB hq0 hq M N x 4 hi8).trans_lt h8⟩

end
end ASDExplicitGamma.Inverse
