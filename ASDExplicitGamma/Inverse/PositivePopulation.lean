module

public import ASDExplicitGamma.Inverse.PositiveSplit

/-! Exact order-128 population payment for the positive inverse-bank remainders. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal

theorem positive_finite_max_pow_le {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (s.sup f)^128 ≤ ∑ i ∈ s, (f i)^128 := by
  rw [Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x : ℝ≥0∞ => x^128)
    (fun _ _ h => pow_le_pow_left' h 128) (by norm_num)]
  apply Finset.sup_le
  intro i hi
  exact Finset.single_le_sum (fun j _ => (zero_le : (0:ℝ≥0∞) ≤ (f j)^128)) hi

theorem positive_L128_formula {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    eLpNorm f 128 mu = (∫⁻ ω, (f ω)^128 ∂mu)^(1/128 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  norm_num [enorm_eq_self]

theorem positive_L128_power {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    (eLpNorm f 128 mu)^128 = ∫⁻ ω, (f ω)^128 ∂mu := by
  rw [positive_L128_formula mu f hf,← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
  norm_num

/-- The exact population cost is card(s)^(1/128), not card(s). -/
theorem positive_finite_max_L128 {ι Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (s : Finset ι) (f : ι → Ω → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (B : ℝ≥0∞)
    (hB : ∀ i ∈ s, eLpNorm (f i) 128 mu ≤ B) :
    eLpNorm (historyFiniteMax s f) 128 mu ≤ (s.card : ℝ≥0∞)^(1/128 : ℝ)*B := by
  have hmoment : (∫⁻ ω, (historyFiniteMax s f ω)^128 ∂mu) ≤ (s.card : ℝ≥0∞)*B^128 := by
    calc
      _ ≤ ∫⁻ ω, ∑ i ∈ s, (f i ω)^128 ∂mu := lintegral_mono (fun ω => positive_finite_max_pow_le s (fun i => f i ω))
      _ = ∑ i ∈ s, ∫⁻ ω, (f i ω)^128 ∂mu := lintegral_finsetSum _ (fun i _ => (hf i).pow_const 128)
      _ ≤ ∑ _i ∈ s, B^128 := Finset.sum_le_sum (fun i hi => by
        rw [← positive_L128_power mu (f i) (hf i)]
        exact pow_le_pow_left' (hB i hi) 128)
      _ = (s.card : ℝ≥0∞)*B^128 := by simp only [Finset.sum_const, nsmul_eq_mul]
  rw [positive_L128_formula mu _ (history_finite_max_measurable s f hf)]
  have h := ENNReal.rpow_le_rpow hmoment (by norm_num : (0:ℝ) ≤ 1/128)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at h
  have hp : (B^128)^(1/128 : ℝ) = B := by
    rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
    norm_num
  rwa [hp] at h

/-- The exact population/grouping inequalities are supplied by the native
inverse numeric certificates, with no rounded population root. -/
theorem positive_population_payments :
    (Numerics.Inverse.invPopulationRoot : ℝ) ^ 128 > (9 : ℝ) ^ 44 ∧
    (509 / 500 : ℝ) ^ 128 > 9 ∧ (5 : ℝ) ^ 128 > 9 ^ 89 := by
  have h := Numerics.Inverse.invPopulation_payment
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast h.1
  · have hh : (((509 / 500 : ℚ) : ℝ) ^ 128) > (9 : ℝ) := by exact_mod_cast h.2.1
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hh
  · exact_mod_cast h.2.2

end ASDExplicitGamma.Inverse
