module

public import ASDExplicitGamma.Inverse.BankInverse

/-! Source observer grouping, charging only the positive remainders. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

noncomputable def inverseBankGroupedHistory {ι : Type*} (I : Finset ι)
    (families : ι → Finset (TriadicCube 2)) (M : ABKModel 2) (m J : ℤ)
    (weights : ℤ → ℝ) : Cutoff.CutoffSample 2 → ℝ≥0∞ :=
  historyFiniteMax I (fun i => bankFiniteRootHistoryMax (families i) M m J weights)

noncomputable def inverseBankGroupedRemainder {ι : Type*} (r : InverseBankRow) (I : Finset ι)
    (families : ι → Finset (TriadicCube 2)) (M : ABKModel 2) (m J : ℤ)
    (weights : ℤ → ℝ) : Cutoff.CutoffSample 2 → ℝ≥0∞ :=
  historyFiniteMax I (fun i ω => ENNReal.ofReal
    (inverseBankPopulationRemainder r (families i) M m J weights ω))

theorem bank_scalar_grouping_payment (n : ℕ) (hn : n ≤ 9^89) :
    (n:ℝ≥0∞)^(1/128:ℝ) ≤ 5 := by
  have hcard : (n:ℝ≥0∞) ≤ (9:ℝ≥0∞)^89 := by exact_mod_cast hn
  have hfive : (9:ℝ≥0∞)^89 ≤ (5:ℝ≥0∞)^128 := by
    exact_mod_cast ASDExplicitGamma.Numerics.Inverse.invPopulation_payment.2.2.le
  have hh := ENNReal.rpow_le_rpow (hcard.trans hfive) (by norm_num : (0:ℝ) ≤ 1/128)
  have he : ((5:ℝ≥0∞)^128)^(1/128:ℝ) = 5 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rwa [he] at hh

/-- The 9^89 ordinary observer union pays at most five on the rare part.
Its baseline remains A+delta and the total is bounded separately using the
strict grouped profile comparison. No independence is assumed. -/
theorem inverse_bank_grouped {ι : Type*}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (r : InverseBankRow) (I : Finset ι)
    (families : ι → Finset (TriadicCube 2)) (hI : I.card ≤ 9^89)
    (m J : ℤ) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (hscale : ∀ i ∈ I, ∀ Q ∈ families i, Q.scale ≤ m ∧ m-Q.scale ≤ 5)
    (hcard : ∀ i ∈ I, (families i).card ≤ 6*9^45)
    (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m (inverseBankRootRow r)) :
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      inverseBankGroupedHistory I families M m J weights ω ≤
        ENNReal.ofReal ((inverseBankA r:ℝ)+1/2000) +
          inverseBankGroupedRemainder r I families M m J weights ω) ∧
      eLpNorm (inverseBankGroupedRemainder r I families M m J weights) 128
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (5*(inverseBankReserve r:ℝ)) ∧
      eLpNorm (inverseBankGroupedHistory I families M m J weights) 128
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (inverseBankCap r:ℝ) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let H := fun i => bankFiniteRootHistoryMax (families i) M m J weights
  let R := fun i => inverseBankPopulationRemainder r (families i) M m J weights
  have hBank (i : ι) (hi : i ∈ I) := inverse_bank_population M h hM hg r
    (families i) m J hmJ weights hw (hscale i hi) (hcard i hi) hpast hmean
  have hHm (i : ι) : Measurable (H i) :=
    history_finite_max_measurable _ _ (fun Q => bank_root_inverse_history_measurable Q.1 M m J weights)
  have hRm (i : ι) : Measurable (R i) :=
    inverse_bank_population_remainder_measurable r (families i) M m J weights
  have hR0 (i : ι) (ω : Cutoff.CutoffSample 2) : 0 ≤ R i ω :=
    (positive_split (H i ω).toReal (inverseBankA r:ℝ) (1/2000)).1
  have hA0 := (inverse_bank_profile_nonneg r).1
  have hAd0 : 0 ≤ (inverseBankA r:ℝ)+1/2000 := add_nonneg hA0 (by norm_num)
  have hEps0 : 0 ≤ (inverseBankReserve r:ℝ) := by cases r <;> norm_num [inverseBankReserve]
  have hSplit (i : ↥I) : ∀ᵐ ω ∂μ, H i.1 ω ≤
      ENNReal.ofReal ((inverseBankA r:ℝ)+1/2000)+ENNReal.ofReal (R i.1 ω) := by
    filter_upwards [(hBank i.1 i.2).history_finite] with ω hω
    have hh := ENNReal.ofReal_le_ofReal
      (positive_split (H i.1 ω).toReal (inverseBankA r:ℝ) (1/2000)).2
    rw [ENNReal.ofReal_toReal hω.ne] at hh
    change H i.1 ω ≤ ENNReal.ofReal ((inverseBankA r:ℝ)+1/2000+R i.1 ω) at hh
    rw [ENNReal.ofReal_add hAd0 (hR0 i.1 ω)] at hh
    exact hh
  have hGroupedSplit : ∀ᵐ ω ∂μ, inverseBankGroupedHistory I families M m J weights ω ≤
      ENNReal.ofReal ((inverseBankA r:ℝ)+1/2000)+
        inverseBankGroupedRemainder r I families M m J weights ω := by
    filter_upwards [ae_all_iff.mpr hSplit] with ω hω
    change I.sup (fun i => H i ω) ≤ _
    apply Finset.sup_le
    intro i hi
    exact (hω ⟨i,hi⟩).trans (add_le_add le_rfl
      (Finset.le_sup (f := fun i => ENNReal.ofReal (R i ω)) hi))
  have hPop := positive_finite_max_L128 μ I (fun i ω => ENNReal.ofReal (R i ω))
    (fun i => ENNReal.continuous_ofReal.measurable.comp (hRm i))
    (ENNReal.ofReal (inverseBankReserve r:ℝ)) (fun i hi => by
      change eLpNorm (ENNReal.ofReal ∘ R i) 128 μ ≤ _
      rw [eLpNorm_ofReal (R i) (Filter.Eventually.of_forall (hR0 i))]
      exact (hBank i hi).remainder_L128)
  have hGroupedR : eLpNorm (inverseBankGroupedRemainder r I families M m J weights) 128 μ ≤
      ENNReal.ofReal (5*(inverseBankReserve r:ℝ)) := by
    calc
      _ ≤ (I.card:ℝ≥0∞)^(1/128:ℝ)*ENNReal.ofReal (inverseBankReserve r:ℝ) := hPop
      _ ≤ 5*ENNReal.ofReal (inverseBankReserve r:ℝ) :=
        mul_le_mul_of_nonneg_right (bank_scalar_grouping_payment I.card hI) bot_le
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5)]; norm_num
  have hHgroup : Measurable (inverseBankGroupedHistory I families M m J weights) :=
    history_finite_max_measurable _ _ hHm
  let C : ℝ≥0∞ := ENNReal.ofReal ((inverseBankA r:ℝ)+1/2000)
  have hConst : eLpNorm (fun _ : Cutoff.CutoffSample 2 => C) 128 μ = C := by
    rw [eLpNorm_const' C (by norm_num) (by norm_num)]
    simp only [enorm_eq_self, measure_univ, ENNReal.one_rpow, mul_one]
  refine ⟨hGroupedSplit,hGroupedR,?_⟩
  calc
    _ ≤ eLpNorm ((fun _ => C)+inverseBankGroupedRemainder r I families M m J weights) 128 μ :=
      eLpNorm_mono_enorm_ae hHgroup.aestronglyMeasurable
        (hGroupedSplit.mono fun ω hω => by
          simpa only [enorm_eq_self, Pi.add_apply, C] using hω)
    _ ≤ eLpNorm (fun _ : Cutoff.CutoffSample 2 => C) 128 μ +
        eLpNorm (inverseBankGroupedRemainder r I families M m J weights) 128 μ :=
      eLpNorm_add_le (by norm_num)
    _ ≤ C+ENNReal.ofReal (5*(inverseBankReserve r:ℝ)) := by
      rw [hConst]
      exact add_le_add le_rfl hGroupedR
    _ = ENNReal.ofReal ((inverseBankA r:ℝ)+1/2000+5*(inverseBankReserve r:ℝ)) :=
      (ENNReal.ofReal_add hAd0 (mul_nonneg (by norm_num) hEps0)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (inverse_bank_grouped_numeric_bound r).le

end ASDExplicitGamma.Inverse
