module

public import ASDExplicitGamma.Inverse.BankDepthArithmetic
public import ASDExplicitGamma.Inverse.BankInverse

/-! Complete inverse-history population bounds at every additional depth. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

noncomputable def inverseBankDepthHistoryRemainder (r : InverseBankRow)
    (s : Finset (TriadicCube 2)) (M : ABKModel 2) (m J : ℤ) (weights : ℤ → ℝ) (j : ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  positiveSplitRemainder (bankFiniteRootHistoryMax s M m J weights ω).toReal
    (inverseBankDepthA r M j) (inverseBankDepthSlack M j)

structure InverseBankDepthConclusion (M : ABKModel 2) (r : InverseBankRow)
    (s : Finset (TriadicCube 2)) (m J : ℤ) (weights : ℤ → ℝ) (j : ℕ) : Prop where
  history_finite : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
    bankFiniteRootHistoryMax s M m J weights ω < ∞
  remainder_measurable : Measurable (inverseBankDepthHistoryRemainder r s M m J weights j)
  remainder_nonneg : ∀ ω, 0 ≤ inverseBankDepthHistoryRemainder r s M m J weights j ω
  history_le : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
    bankFiniteRootHistoryMax s M m J weights ω ≤
      ENNReal.ofReal ((inverseBankCap r:ℝ)*bankDepthFrame M j) +
        ENNReal.ofReal (inverseBankDepthHistoryRemainder r s M m J weights j ω)
  remainder_L128 : eLpNorm (inverseBankDepthHistoryRemainder r s M m J weights j) 128
    (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (inverseBankDepthReserve r M j)

theorem inverse_bank_depth_history_pretruncation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (r : InverseBankRow) (s : Finset (TriadicCube 2))
    (m J : ℤ) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1) (j : ℕ)
    (hscale : ∀ Q ∈ s, Q.scale ≤ m-(j:ℤ) ∧ (m-(j:ℤ))-Q.scale ≤ 5)
    (hcard : s.card ≤ 6*9^(45+j)) (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m (inverseBankRootRow r)) :
    Measurable (bankFiniteRootHistoryMax s M m J weights) ∧
      Measurable (bankFiniteRootRemainderHistoryMax s M m (inverseBankRootRow r)) ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        bankFiniteRootHistoryMax s M m J weights ω ≤ ENNReal.ofReal (inverseBankDepthA r M j) +
          bankFiniteRootRemainderHistoryMax s M m (inverseBankRootRow r) ω) ∧
      eLpNorm (bankFiniteRootRemainderHistoryMax s M m (inverseBankRootRow r)) 256
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (inverseBankDepthE r M j) := by
  have hscope : ∀ Q ∈ s, Q.scale ≤ m := by
    intro Q hQ
    have := (hscale Q hQ).1
    omega
  have hBase (Q : TriadicCube 2) (hQ : Q ∈ s) :=
    inverse_bank_depth_baseline_cap M hg Q m j r (hscale Q hQ).1 (hscale Q hQ).2
  have hCap (Q : TriadicCube 2) (hQ : Q ∈ s) : eLpNorm
      (bankRootInverseRemainderHistory Q M m (inverseBankRootRow r)) 256
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
          ENNReal.ofReal (bankDepthFrame M j)*inverseBankRootErrorCap r := by
    have hh := bank_root_inverse_remainder_history_L256_of_pointwise M h hM hg Q m J
      (hscope Q hQ) hmJ weights hw (inverseBankRootRow r) hpast hmean
      (q3_pointwise_root M h hM hg)
    exact hh.trans (inverse_bank_depth_remainder_budget_cap M hg Q m j r
      (hscale Q hQ).1 (hscale Q hQ).2)
  obtain ⟨hY,hR,hSplit,hN⟩ := bank_finite_history_split_of_root_caps M h hM hg
    (inverseBankRootRow r) s m J hmJ weights hw hscope hpast hmean
    (inverseBankDepthA r M j) (ENNReal.ofReal (bankDepthFrame M j)*inverseBankRootErrorCap r)
    hBase hCap
  refine ⟨hY,hR,hSplit,?_⟩
  calc
    _ ≤ (s.card:ℝ≥0∞)^(1/256:ℝ)*
        (ENNReal.ofReal (bankDepthFrame M j)*inverseBankRootErrorCap r) := hN
    _ ≤ ((ENNReal.ofReal (509/500:ℝ)*
          ENNReal.ofReal (ASDExplicitGamma.Numerics.Inverse.invPopulationRoot:ℝ))*
          (9:ℝ≥0∞)^((j:ℝ)/256))*
        (ENNReal.ofReal (bankDepthFrame M j)*inverseBankRootErrorCap r) :=
      mul_le_mul_of_nonneg_right (bank_root_population_payment_depth s.card j hcard) bot_le
    _ = ENNReal.ofReal (inverseBankE r:ℝ)*ENNReal.ofReal (bankDepthFrame M j)*
        (9:ℝ≥0∞)^((j:ℝ)/256) := by
      rw [← inverse_bank_remainder_ofReal r]
      ac_rfl
    _ = _ := inverse_bank_depth_E_ofReal r M j

/-- Source (10.9), with true powers at every unbounded additional depth.
This is the depth maximum of complete histories, rather than a uniform
total-moment claim for the entire unbounded population. -/
theorem inverse_bank_depth_history
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (r : InverseBankRow) (s : Finset (TriadicCube 2))
    (m J : ℤ) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1) (j : ℕ)
    (hscale : ∀ Q ∈ s, Q.scale ≤ m-(j:ℤ) ∧ (m-(j:ℤ))-Q.scale ≤ 5)
    (hcard : s.card ≤ 6*9^(45+j)) (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m (inverseBankRootRow r)) :
    InverseBankDepthConclusion M r s m J weights j := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Y := bankFiniteRootHistoryMax s M m J weights
  let R := bankFiniteRootRemainderHistoryMax s M m (inverseBankRootRow r)
  let y : Cutoff.CutoffSample 2 → ℝ := fun ω => (Y ω).toReal
  obtain ⟨hY,hR,hSplit,hR256⟩ := inverse_bank_depth_history_pretruncation M h hM hg r s
    m J hmJ weights hw j hscale hcard hpast hmean
  have hRfinite := bank_L256_ae_finite μ R hR (inverseBankDepthE r M j) hR256
  have hYfinite : ∀ᵐ ω ∂μ, Y ω < ∞ := by
    filter_upwards [hSplit,hRfinite] with ω hω hrω
    exact lt_of_le_of_lt hω (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,hrω⟩)
  have hy : Measurable y := ENNReal.measurable_toReal.comp hY
  obtain ⟨hA0,he0,hδ⟩ := inverse_bank_depth_nonneg r M j
  have hbounds := inverse_bank_depth_profile_bounds r M j
  have hb0 : 0 ≤ (inverseBankCap r:ℝ)*bankDepthFrame M j :=
    (add_nonneg hA0 hδ.le).trans hbounds.1
  have hP := (bank_ennreal_positive_split_L128_of_affine μ Y R hY hR
    (inverseBankDepthA r M j) (inverseBankDepthSlack M j) (inverseBankDepthE r M j)
      hA0 hδ he0 hSplit hR256).2
  have hNonneg (ω : Cutoff.CutoffSample 2) :
      0 ≤ inverseBankDepthHistoryRemainder r s M m J weights j ω :=
    (positive_split (y ω) (inverseBankDepthA r M j) (inverseBankDepthSlack M j)).1
  have hRealSplit (ω : Cutoff.CutoffSample 2) : y ω ≤
      (inverseBankCap r:ℝ)*bankDepthFrame M j+inverseBankDepthHistoryRemainder r s M m J weights j ω :=
    (positive_split (y ω) (inverseBankDepthA r M j) (inverseBankDepthSlack M j)).2.trans
      (add_le_add hbounds.1 le_rfl)
  refine ⟨hYfinite,?_,hNonneg,?_,?_⟩
  · exact measurable_const.max ((hy.sub_const (inverseBankDepthA r M j)).sub_const (inverseBankDepthSlack M j))
  · filter_upwards [hYfinite] with ω hω
    have hh := ENNReal.ofReal_le_ofReal (hRealSplit ω)
    rw [ENNReal.ofReal_toReal hω.ne, ENNReal.ofReal_add hb0 (hNonneg ω)] at hh
    exact hh
  · calc
      _ ≤ ENNReal.ofReal (1/(4*inverseBankDepthSlack M j))*
          ENNReal.ofReal (inverseBankDepthE r M j)^2 := hP
      _ = ENNReal.ofReal ((inverseBankDepthE r M j)^2/(4*inverseBankDepthSlack M j)) := by
        rw [← ENNReal.ofReal_pow he0, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal hbounds.2

end ASDExplicitGamma.Inverse
