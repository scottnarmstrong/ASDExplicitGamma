module

public import ASDExplicitGamma.Inverse.BankInversePopulation

/-! Total and positive-split inverse banks for actual attenuated laws. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

/-- Source observer-bank conclusions, on the actual extended complete
histories. Finiteness is explicit before any real-valued truncation is used. -/
structure InverseBankConclusion (M : ABKModel 2) (r : InverseBankRow)
    (s : Finset (TriadicCube 2)) (m J : ℤ) (weights : ℤ → ℝ) : Prop where
  history_finite : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
    bankFiniteRootHistoryMax s M m J weights ω < ∞
  remainder_measurable : Measurable (inverseBankPopulationRemainder r s M m J weights)
  remainder_nonneg : ∀ ω, 0 ≤ inverseBankPopulationRemainder r s M m J weights ω
  history_le : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
    bankFiniteRootHistoryMax s M m J weights ω ≤ ENNReal.ofReal (inverseBankCap r:ℝ) +
      ENNReal.ofReal (inverseBankPopulationRemainder r s M m J weights ω)
  total_L128 : eLpNorm (bankFiniteRootHistoryMax s M m J weights) 128
    (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (inverseBankCap r:ℝ)
  remainder_L128 : eLpNorm (inverseBankPopulationRemainder r s M m J weights) 128
    (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (inverseBankReserve r:ℝ)

theorem bank_L256_ae_finite {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : Ω → ℝ≥0∞) (hR : Measurable R) (e : ℝ)
    (he : eLpNorm R 256 μ ≤ ENNReal.ofReal e) : ∀ᵐ ω ∂μ, R ω < ∞ := by
  have hp : (eLpNorm R 256 μ)^256 ≤ (ENNReal.ofReal e)^256 := pow_le_pow_left' he 256
  have hi : (∫⁻ ω, (R ω)^256 ∂μ) ≠ ∞ := by
    rw [← bank_L256_power μ R hR]
    exact ne_top_of_le_ne_top (by simp) hp
  have ha : ∀ᵐ ω ∂μ, (R ω)^256 < ∞ := ae_lt_top (hR.pow_const 256) hi
  filter_upwards [ha] with ω hω
  by_contra hn
  have ht : R ω = ∞ := by simpa using hn
  simp only [ht, ENNReal.top_pow (by norm_num : (256:ℕ) ≠ 0), lt_self_iff_false] at hω

/-- The complete actual observer bank, with the exact source total and rare
reserve, uniform over every finite deterministic attenuation vector. -/
theorem inverse_bank_population
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (r : InverseBankRow)
    (s : Finset (TriadicCube 2)) (m J : ℤ) (hmJ : m ≤ J)
    (weights : ℤ → ℝ) (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (hscale : ∀ Q ∈ s, Q.scale ≤ m ∧ m-Q.scale ≤ 5) (hcard : s.card ≤ 6*9^45)
    (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m (inverseBankRootRow r)) :
    InverseBankConclusion M r s m J weights := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Y := bankFiniteRootHistoryMax s M m J weights
  let R := bankFiniteRootRemainderHistoryMax s M m (inverseBankRootRow r)
  let y : Cutoff.CutoffSample 2 → ℝ := fun ω => (Y ω).toReal
  obtain ⟨hY,hR,hSplit,hR256⟩ := inverse_bank_population_pretruncation
    M h hM hg r s m J hmJ weights hw hscale hcard hpast hmean
  have hRfinite := bank_L256_ae_finite μ R hR (inverseBankE r:ℝ) hR256
  have hYfinite : ∀ᵐ ω ∂μ, Y ω < ∞ := by
    filter_upwards [hSplit,hRfinite] with ω hω hrω
    exact lt_of_le_of_lt hω (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,hrω⟩)
  have hy : Measurable y := ENNReal.measurable_toReal.comp hY
  have hA0 := (inverse_bank_profile_nonneg r).1
  have he0 := (inverse_bank_profile_nonneg r).2.1
  obtain ⟨htotal,hslack,hreserve⟩ := inverse_bank_numeric_bounds r
  have hb0 : 0 ≤ (inverseBankCap r:ℝ) :=
    (add_nonneg hA0 (by norm_num : (0:ℝ) ≤ 1/2000)).trans hslack.le
  obtain ⟨hT,hP⟩ := bank_ennreal_positive_split_L128_of_affine μ Y R hY hR
    (inverseBankA r:ℝ) (1/2000) (inverseBankE r:ℝ) hA0 (by norm_num) he0 hSplit hR256
  have hT' : eLpNorm y 128 μ ≤ ENNReal.ofReal (inverseBankCap r:ℝ) := by
    calc
      _ ≤ ENNReal.ofReal (inverseBankA r:ℝ)+ENNReal.ofReal (inverseBankE r:ℝ) := hT
      _ = ENNReal.ofReal ((inverseBankA r:ℝ)+(inverseBankE r:ℝ)) :=
        (ENNReal.ofReal_add hA0 he0).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal htotal.le
  have hNorm : eLpNorm Y 128 μ = eLpNorm y 128 μ := by
    calc
      _ = eLpNorm (fun ω => ENNReal.ofReal (y ω)) 128 μ :=
        (eLpNorm_congr_ae (ofReal_toReal_ae_eq hYfinite)).symm
      _ = _ := eLpNorm_ofReal y (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
  have hRemNonneg (ω : Cutoff.CutoffSample 2) :
      0 ≤ inverseBankPopulationRemainder r s M m J weights ω :=
    (positive_split (y ω) (inverseBankA r:ℝ) (1/2000)).1
  have hRealSplit (ω : Cutoff.CutoffSample 2) : y ω ≤ (inverseBankCap r:ℝ)+
      inverseBankPopulationRemainder r s M m J weights ω :=
    (positive_split (y ω) (inverseBankA r:ℝ) (1/2000)).2.trans
      (add_le_add hslack.le le_rfl)
  refine ⟨hYfinite,?_,hRemNonneg,?_,hNorm.trans_le hT',?_⟩
  · exact measurable_const.max ((hy.sub_const (inverseBankA r:ℝ)).sub_const (1/2000))
  · filter_upwards [hYfinite] with ω hω
    have hh := ENNReal.ofReal_le_ofReal (hRealSplit ω)
    rw [ENNReal.ofReal_toReal hω.ne, ENNReal.ofReal_add hb0 (hRemNonneg ω)] at hh
    exact hh
  · calc
      _ ≤ ENNReal.ofReal (1/(4*(1/2000):ℝ))*ENNReal.ofReal (inverseBankE r:ℝ)^2 := hP
      _ = ENNReal.ofReal ((inverseBankE r:ℝ)^2/(4*(1/2000:ℝ))) := by
        rw [← ENNReal.ofReal_pow he0, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreserve.le

/-- First-local inverse observer bank: 1.5900 total and 3*10^-46 rare reserve.
The earlier native states supply its clipped full-matrix mean. -/
theorem first_local_inverse_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (s : Finset (TriadicCube 2)) (m J : ℤ) (hmJ : m ≤ J)
    (weights : ℤ → ℝ) (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (hscale : ∀ Q ∈ s, Q.scale ≤ m ∧ m-Q.scale ≤ 5) (hcard : s.card ≤ 6*9^45)
    (hpast : ∀ n < m, nativeInductionState M h n) :
    InverseBankConclusion M .firstLocal s m J weights := by
  exact inverse_bank_population M h hM hg .firstLocal s m J hmJ weights hw hscale hcard hpast
    (clipped_inverse_mean_input_first_full M h hg m .firstLocal (Or.inl rfl) hpast)

/-- Global inverse observer bank in the OLD true frame, using its strictly
earlier one-pass directional inverse mean. -/
theorem global_inverse_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (s : Finset (TriadicCube 2)) (m J : ℤ) (hmJ : m ≤ J)
    (weights : ℤ → ℝ) (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (hscale : ∀ Q ∈ s, Q.scale ≤ m ∧ m-Q.scale ≤ 5) (hcard : s.card ≤ 6*9^45)
    (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m .globalInverse) :
    InverseBankConclusion M .globalInverse s m J weights :=
  inverse_bank_population M h hM hg .globalInverse s m J hmJ weights hw hscale hcard hpast hmean

/-- OLD local inverse observer bank, uniformly over every finite band and
deterministic attenuation, including the union of source refinements. -/
theorem local_inverse_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (s : Finset (TriadicCube 2)) (m J : ℤ) (hmJ : m ≤ J)
    (weights : ℤ → ℝ) (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (hscale : ∀ Q ∈ s, Q.scale ≤ m ∧ m-Q.scale ≤ 5) (hcard : s.card ≤ 6*9^45)
    (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m .localInverse) :
    InverseBankConclusion M .localInverse s m J weights :=
  inverse_bank_population M h hM hg .localInverse s m J hmJ weights hw hscale hcard hpast hmean

end ASDExplicitGamma.Inverse
