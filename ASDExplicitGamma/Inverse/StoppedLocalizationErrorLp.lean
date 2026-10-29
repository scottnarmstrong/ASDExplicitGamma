module

public import ASDExplicitGamma.Inverse.StoppedLocalizationMismatch
public import ASDExplicitGamma.Inverse.StoppedDiameterLp
public import ASDExplicitGamma.Inverse.StoppedMismatchHolder

/-! Exact real-order source localization error without independence from the diameter. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The literal source power error, retaining its full diameter outside the
inspection box instead of inserting an artificial localization-size term. -/
def localizationPowerError {Ω : Type*} (B : PlanarMarks Ω) (M m : ℕ)
    (x : BlockSite) (ω : Ω) : ℝ :=
  (realDiameterField B x ω)^m-(realLocalizedDiameterField B M (3^M) x ω)^m

theorem nonnegative_power_difference_le (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (m : ℕ) :
    |a^m-b^m| ≤ if b ≠ a then a^m else 0 := by
  classical
  by_cases he : b ≠ a
  · rw [ite_eq_left he,abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hb hba m))]
    have hh := pow_nonneg hb m
    linarith only [hh]
  · have he' : b = a := not_ne_iff.mp he
    simp only [he',ne_eq,not_true_eq_false,ite_false,sub_self,abs_zero,le_refl]

/-- Exact QSEP localization error for all real p>=1 and positive integer m.
The diameter, event, and inspected field may be arbitrarily correlated. -/
theorem localization_power_error_Lp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hfloor : Real.exp (-6000) ≤ q) (M m : ℕ) (hm : 1 ≤ m)
    (x : BlockSite) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (localizationPowerError B M m x) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal ((80*(m:ℝ)*p)^m*(12000:ℝ)^(1/(2*p))*Real.exp (-(3:ℝ)^M/(6*p))) := by
  classical
  let E : Set Ω := {ω | realLocalizedDiameterField B M (3^M) x ω ≠ realDiameterField B x ω}
  let X : Ω → ℝ := fun ω => (realDiameterField B x ω)^m
  have hZ := real_diameter_measurable B hB.local_measurable hB.positive_measurable x
  have hL := real_localized_diameter_measurable B hB.local_measurable hB.positive_measurable M (3^M) x
  have hE : MeasurableSet E := by
    exact (measurableSet_eq_fun hL hZ).compl
  have hX : Measurable X := hZ.pow_const m
  have hD : Measurable (localizationPowerError B M m x) := (hZ.pow_const m).sub (hL.pow_const m)
  have hdom : eLpNorm (localizationPowerError B M m x) (ENNReal.ofReal p) μ ≤
      eLpNorm (E.indicator X) (ENNReal.ofReal p) μ := by
    apply eLpNorm_mono_ae_real hD.aestronglyMeasurable
    filter_upwards [real_localized_diameter_ae_le μ B q hB hq0 hq] with ω hω
    have hh := nonnegative_power_difference_le (realDiameterField B x ω)
      (realLocalizedDiameterField B M (3^M) x ω)
      (real_localized_diameter_bounds B M (3^M) x ω).1 (hω M (3^M) x) m
    simpa only [Real.norm_eq_abs,localizationPowerError,E,X,Set.indicator,Set.mem_ofPred_eq] using! hh
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hprod : (1:ℝ) ≤ p*(m:ℝ) := by
    simpa only [one_mul] using mul_le_mul hp hmR (by norm_num : (0:ℝ) ≤ 1) hp0.le
  have horder : (1:ℝ) ≤ (2*p)*(m:ℝ) := by nlinarith only [hprod]
  have hbase := real_diameter_Lp μ B q hB hq0 hq hfloor x ((2*p)*(m:ℝ)) horder
  have hbase' : eLpNorm (realDiameterField B x) (ENNReal.ofReal ((2*p)*(m:ℝ))) μ ≤
      ENNReal.ofReal (80*(m:ℝ)*p) := by
    convert hbase using 1
    congr 1
    ring
  have hnorm : eLpNorm X (ENNReal.ofReal (2*p)) μ ≤ ENNReal.ofReal ((80*(m:ℝ)*p)^m) := by
    rw [nonnegative_power_eLpNorm μ _ hZ.aestronglyMeasurable (fun _ => ENNReal.toReal_nonneg)
      m (by omega) (2*p) (by positivity),ENNReal.ofReal_pow (by positivity)]
    exact pow_le_pow_left' hbase' m
  have hprob : μ E ≤ ENNReal.ofReal (12000*Real.exp (-(3:ℝ)^M/3)) :=
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (by positivity)).mpr
      (real_localized_diameter_mismatch_probability μ B q hB hq0 hq M x)
  have hpow := ENNReal.rpow_le_rpow hprob (by positivity : 0 ≤ (1/(2*p):ℝ))
  calc
    _ ≤ eLpNorm (E.indicator X) (ENNReal.ofReal p) μ := hdom
    _ ≤ eLpNorm X (ENNReal.ofReal (2*p)) μ*(μ E)^(1/(2*p):ℝ) :=
      indicator_holder μ X hX.aestronglyMeasurable E hE p hp0
    _ ≤ ENNReal.ofReal ((80*(m:ℝ)*p)^m)*
        (ENNReal.ofReal (12000*Real.exp (-(3:ℝ)^M/3)))^(1/(2*p):ℝ) :=
      mul_le_mul hnorm hpow (zero_le : (0:ℝ≥0∞) ≤ _) (zero_le : (0:ℝ≥0∞) ≤ _)
    _ = _ := by
      rw [mismatch_exponential_payment _ p,← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end
end ASDExplicitGamma.Inverse
