module

public import ASDExplicitGamma.Inverse.StoppedLocalizationEscape
public import ASDExplicitGamma.Inverse.StoppedOmittedProbability
public import ASDExplicitGamma.Inverse.StoppedRealDiameter

/-! The actual source localization mismatch probability on the full probability space. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
noncomputable section

/-- The literal source mismatch probability, N=3^M, with the full infinite
label family and all components meeting the radius-two neighborhood. -/
theorem localized_diameter_mismatch_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (M : ℕ) (x : BlockSite) :
    μ.real {ω | localizedDiameterField B M (3^M) x ω ≠ diameterField B ω x} ≤
      12000*Real.exp (-(3:ℝ)^M/3) := by
  have hN : (0:ℝ) ≤ 3^M := by positivity
  have hhalf : Real.exp (-(3:ℝ)^M/2) ≤ Real.exp (-(3:ℝ)^M/3) :=
    Real.exp_le_exp.mpr (by linarith only [hN])
  have hfull : Real.exp (-(3:ℝ)^M) ≤ Real.exp (-(3:ℝ)^M/3) :=
    Real.exp_le_exp.mpr (by linarith only [hN])
  have hescape := localization_escape_probability μ B q hB hq0 hq (3^M) x
  norm_num only [Nat.cast_pow,Nat.cast_ofNat] at hescape
  calc
    _ ≤ μ.real (localizationEscape B (3^M) x ∪ omittedActivation B M (3^M) x) :=
      measureReal_mono (localized_diameter_mismatch_subset B M (3^M) x) (measure_ne_top μ _)
    _ ≤ μ.real (localizationEscape B (3^M) x)+μ.real (omittedActivation B M (3^M) x) := measureReal_union_le _ _
    _ ≤ 75*Real.exp (-(3:ℝ)^M/2)+Real.exp (-(3:ℝ)^M) :=
      add_le_add hescape (omitted_activation_probability μ B q hB M x)
    _ ≤ _ := by
      have he := Real.exp_pos (-(3:ℝ)^M/3)
      nlinarith only [hhalf,hfull,he]

/-- The ordinary real source fields have the same mismatch upper bound,
including their stated convention on the full-field null exceptional set. -/
theorem real_localized_diameter_mismatch_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (M : ℕ) (x : BlockSite) :
    μ.real {ω | realLocalizedDiameterField B M (3^M) x ω ≠ realDiameterField B x ω} ≤
      12000*Real.exp (-(3:ℝ)^M/3) := by
  have hsub : {ω | realLocalizedDiameterField B M (3^M) x ω ≠ realDiameterField B x ω} ⊆
      {ω | localizedDiameterField B M (3^M) x ω ≠ diameterField B ω x} := by
    intro ω hω he
    exact hω (congrArg ENNReal.toReal he)
  exact (measureReal_mono hsub (measure_ne_top μ _)).trans
    (localized_diameter_mismatch_probability μ B q hB hq0 hq M x)

end
end ASDExplicitGamma.Inverse
