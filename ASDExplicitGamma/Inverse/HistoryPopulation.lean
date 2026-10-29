module

public import ASDExplicitGamma.Inverse.HistoryLpSeries
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Sharp L20 population payment for finite maxima, with no independence premise. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal

noncomputable def historyFiniteMax {ι Ω : Type*} (s : Finset ι)
    (f : ι → Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ := s.sup (fun i => f i ω)

theorem history_finite_max_measurable {ι Ω : Type*} [MeasurableSpace Ω]
    (s : Finset ι) (f : ι → Ω → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    Measurable (historyFiniteMax s f) := by
  classical
  change Measurable (fun ω => s.sup (fun i => f i ω))
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty] using measurable_const (a := (⊥:ℝ≥0∞))
  | @insert i s hi ih =>
    simpa only [Finset.sup_insert] using (hf i).max ih

theorem history_finite_max_pow_le {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (s.sup f)^20 ≤ ∑ i ∈ s, (f i)^20 := by
  rw [Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x : ℝ≥0∞ => x^20)
    (fun _ _ h => pow_le_pow_left' h 20) (by norm_num)]
  apply Finset.sup_le
  intro i hi
  exact Finset.single_le_sum (fun j _ => (zero_le : (0:ℝ≥0∞) ≤ (f j)^20)) hi

theorem history_L20_formula {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    eLpNorm f 20 mu = (∫⁻ ω, (f ω)^20 ∂mu)^(1/20 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  norm_num [enorm_eq_self]

theorem history_L20_power {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    (eLpNorm f 20 mu)^20 = ∫⁻ ω, (f ω)^20 ∂mu := by
  rw [history_L20_formula mu f hf,← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
  norm_num

/-- The exact population cost is card(s)^(1/20), not card(s). -/
theorem history_finite_max_L20 {ι Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (s : Finset ι) (f : ι → Ω → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (B : ℝ≥0∞)
    (hB : ∀ i ∈ s, eLpNorm (f i) 20 mu ≤ B) :
    eLpNorm (historyFiniteMax s f) 20 mu ≤ (s.card : ℝ≥0∞)^(1/20 : ℝ)*B := by
  have hmoment : (∫⁻ ω, (historyFiniteMax s f ω)^20 ∂mu) ≤ (s.card : ℝ≥0∞)*B^20 := by
    calc
      _ ≤ ∫⁻ ω, ∑ i ∈ s, (f i ω)^20 ∂mu := lintegral_mono (fun ω => history_finite_max_pow_le s (fun i => f i ω))
      _ = ∑ i ∈ s, ∫⁻ ω, (f i ω)^20 ∂mu := lintegral_finsetSum _ (fun i _ => (hf i).pow_const 20)
      _ ≤ ∑ _i ∈ s, B^20 := Finset.sum_le_sum (fun i hi => by
        rw [← history_L20_power mu (f i) (hf i)]
        exact pow_le_pow_left' (hB i hi) 20)
      _ = (s.card : ℝ≥0∞)*B^20 := by simp only [Finset.sum_const, nsmul_eq_mul]
  rw [history_L20_formula mu _ (history_finite_max_measurable s f hf)]
  have h := ENNReal.rpow_le_rpow hmoment (by norm_num : (0:ℝ) ≤ 1/20)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at h
  have hp : (B^20)^(1/20 : ℝ) = B := by
    rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
    norm_num
  rwa [hp] at h

/-- Exact positive scalar homogeneity of the extended L20 norm. -/
theorem history_constant_mul_L20 {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (c : ℝ≥0∞) (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    eLpNorm (fun ω => c*f ω) 20 mu = c*eLpNorm f 20 mu := by
  rw [history_L20_formula mu _ (hf.const_mul c)]
  simp only [mul_pow]
  rw [lintegral_const_mul (c^20) (hf.pow_const 20),ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hc : (c^20)^(1/20 : ℝ) = c := by
    rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
    norm_num
  rw [hc,← history_L20_formula mu f hf]

end ASDExplicitGamma.Inverse
