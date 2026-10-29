module

public import ASDExplicitGamma.Inverse.StoppedDiameterExcess
public import ASDExplicitGamma.Inverse.StoppedExpMomentLp

/-! The exact source real-order diameter norm bound, with integrability derived. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The actual radius-two diameter field satisfies ||Z||_p<=40p for every
real p>=1, without integer rounding or a diameter moment assumption. -/
theorem real_diameter_Lp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hfloor : Real.exp (-6000) ≤ q) (x : BlockSite) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (realDiameterField B x) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (40*p) := by
  have hZ := real_diameter_measurable B hB.local_measurable hB.positive_measurable x
  have hY := diameter_excess_measurable B hB.local_measurable hB.positive_measurable x
  obtain ⟨hiY,hbY⟩ := diameter_excess_exp_moment μ B q hB hq0 hq hfloor x
  have hnY := nonnegative_exp_moment_Lp μ _ hY (diameter_excess_nonneg B x) hiY hbY p hp
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpE : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hconst : eLpNorm (fun _ : Ω => (24:ℝ)) (ENNReal.ofReal p) μ = ENNReal.ofReal 24 := by
    rw [eLpNorm_const' _ (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top,
      measure_univ,ENNReal.one_rpow,mul_one,Real.enorm_eq_ofReal (by norm_num)]
  have hm : eLpNorm (realDiameterField B x) (ENNReal.ofReal p) μ ≤
      eLpNorm (fun ω => diameterExcess B x ω+24) (ENNReal.ofReal p) μ := by
    apply eLpNorm_mono_real hZ.aestronglyMeasurable
    intro ω
    have hz0 : 0 ≤ realDiameterField B x ω := ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs,abs_of_nonneg hz0]
    have hh : realDiameterField B x ω-24 ≤ diameterExcess B x ω := le_max_left _ _
    linarith only [hh]
  calc
    _ ≤ eLpNorm (fun ω => diameterExcess B x ω+24) (ENNReal.ofReal p) μ := hm
    _ ≤ eLpNorm (diameterExcess B x) (ENNReal.ofReal p) μ+
        eLpNorm (fun _ : Ω => (24:ℝ)) (ENNReal.ofReal p) μ :=
      eLpNorm_add_le hpE
    _ ≤ ENNReal.ofReal (16*p)+ENNReal.ofReal 24 := by rw [hconst]; exact add_le_add hnY le_rfl
    _ = ENNReal.ofReal (16*p+24) := (ENNReal.ofReal_add (by positivity) (by norm_num)).symm
    _ ≤ ENNReal.ofReal (40*p) := ENNReal.ofReal_le_ofReal (by linarith only [hp])

end
end ASDExplicitGamma.Inverse
