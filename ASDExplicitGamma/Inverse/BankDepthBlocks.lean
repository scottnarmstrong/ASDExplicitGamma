module

public import ASDExplicitGamma.Inverse.BankDepthHistory

/-! The distinct depth-j maximum of inverse blocks, without a history sum. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Inverse
open scoped ENNReal

noncomputable def inverseBankDepthBlockRemainder (r : InverseBankRow)
    (s : Finset (TriadicCube 2)) (M : ABKModel 2) (m J : ℤ) (weights : ℤ → ℝ) (j : ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  positiveSplitRemainder (bankFiniteRootResponseMax s M m J weights ω).toReal
    (inverseBankDepthA r M j) (inverseBankDepthSlack M j)

structure InverseBankDepthBlockConclusion (M : ABKModel 2) (r : InverseBankRow)
    (s : Finset (TriadicCube 2)) (m J : ℤ) (weights : ℤ → ℝ) (j : ℕ) : Prop where
  block_finite : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
    bankFiniteRootResponseMax s M m J weights ω < ∞
  remainder_measurable : Measurable (inverseBankDepthBlockRemainder r s M m J weights j)
  remainder_nonneg : ∀ ω, 0 ≤ inverseBankDepthBlockRemainder r s M m J weights j ω
  block_le : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
    bankFiniteRootResponseMax s M m J weights ω ≤
      ENNReal.ofReal ((inverseBankCap r:ℝ)*bankDepthFrame M j) +
        ENNReal.ofReal (inverseBankDepthBlockRemainder r s M m J weights j ω)
  remainder_L128 : eLpNorm (inverseBankDepthBlockRemainder r s M m J weights j) 128
    (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (inverseBankDepthReserve r M j)

theorem inverse_bank_depth_block_pretruncation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (r : InverseBankRow) (s : Finset (TriadicCube 2))
    (m J : ℤ) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1) (j : ℕ)
    (hscale : ∀ Q ∈ s, Q.scale ≤ m-(j:ℤ) ∧ (m-(j:ℤ))-Q.scale ≤ 5)
    (hcard : s.card ≤ 6*9^(45+j)) (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m (inverseBankRootRow r)) :
    Measurable (bankFiniteRootResponseMax s M m J weights) ∧
      Measurable (bankFiniteRootRemainderMax s M m (inverseBankRootRow r)) ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        bankFiniteRootResponseMax s M m J weights ω ≤ ENNReal.ofReal (inverseBankDepthA r M j) +
          bankFiniteRootRemainderMax s M m (inverseBankRootRow r) ω) ∧
      eLpNorm (bankFiniteRootRemainderMax s M m (inverseBankRootRow r)) 256
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (inverseBankDepthE r M j) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hg' : M.gamma ≤ 17/50000 := by simpa [gammaZero] using hg
  have hH0 : 333 ≤ rootH0 (inverseBankRootRow r) := by
    cases r <;> norm_num [inverseBankRootRow, rootH0]
  have hscope (Q : ↥s) : Q.1.scale ≤ m := by have := (hscale Q.1 Q.2).1; omega
  have hPointwise (Q : ↥s) := q3_pointwise_root M h hM hg Q.1 m J (hscope Q)
    hmJ weights hw (inverseBankRootRow r) hpast hmean
  have hSelected (Q : ↥s) : FixedSelectedHeightConclusion M Q.1 (inverseBankRootRow r) := by
    apply q3_fixed_selected_height M h hM hg Q.1 (inverseBankRootRow r)
    intro k hk
    apply hpast
    have := hscope Q
    omega
  have hRawMeas (Q : ↥s) := bank_root_selected_remainder_measurable M Q.1 m J weights
    (inverseBankRootRow r) (hPointwise Q) (hSelected Q)
  have hScaledMeas (Q : ↥s) : Measurable
      (bankRootScaledSelectedRemainder M Q.1 m (inverseBankRootRow r)) :=
    (hRawMeas Q).const_mul _
  have hSR : (1:ℝ≥0∞) ≤ ENNReal.ofReal (invSR:ℝ) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    norm_num [invSR, invAlphaLower, invBetaUpper, invE, invGamma]
  have hErrorCap : (ENNReal.ofReal (invE (11/5*invGamma):ℝ)*
      ENNReal.ofReal (invE (11*invGamma):ℝ))*ENNReal.ofReal (inverseBankRho r:ℝ) ≤
        inverseBankRootErrorCap r := by
    unfold inverseBankRootErrorCap
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hSR
      (by positivity : (0:ℝ≥0∞) ≤ ENNReal.ofReal (invE (11/5*invGamma):ℝ)*
        ENNReal.ofReal (invE (11*invGamma):ℝ)*ENNReal.ofReal (inverseBankRho r:ℝ))
  let B := ENNReal.ofReal (bankDepthFrame M j)*inverseBankRootErrorCap r
  have hCap (Q : ↥s) : eLpNorm
      (bankRootScaledSelectedRemainder M Q.1 m (inverseBankRootRow r)) 256 μ ≤ B := by
    have hraw := bank_root_selected_remainder_L256_of_profile M Q.1 m J weights
      (inverseBankRootRow r) (inverseBankRho r:ℝ) hg' (hPointwise Q) (hSelected Q)
      (inverse_bank_error_bound M hg r)
    change eLpNorm (fun ω => bankRootFrameFactor M Q.1 m *
      bankRootSelectedRemainder M Q.1 (inverseBankRootRow r) ω) 256 μ ≤ B
    rw [bank_constant_mul_L256 μ _ _ (hRawMeas Q)]
    calc
      _ ≤ bankRootFrameFactor M Q.1 m*ENNReal.ofReal (inverseBankRho r:ℝ) :=
        mul_le_mul_of_nonneg_left hraw bot_le
      _ ≤ (ENNReal.ofReal (bankDepthFrame M j) *
          (ENNReal.ofReal (invE (11/5*invGamma):ℝ)*ENNReal.ofReal (invE (11*invGamma):ℝ)))*
          ENNReal.ofReal (inverseBankRho r:ℝ) :=
        mul_le_mul_of_nonneg_right (bank_root_depth_frame_factor_cap M hg Q.1 m j
          (hscale Q.1 Q.2).1 (hscale Q.1 Q.2).2) bot_le
      _ ≤ B := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hErrorCap bot_le
  have hSplit (Q : ↥s) : ∀ᵐ ω ∂μ,
      ENNReal.ofReal (rootInverseResponse M Q.1 m J weights ω) ≤
        ENNReal.ofReal (inverseBankDepthA r M j)+
          bankRootScaledSelectedRemainder M Q.1 m (inverseBankRootRow r) ω := by
    filter_upwards [bank_root_inverse_response_le_baseline_add_remainder M Q.1 m J weights
      (inverseBankRootRow r) (hPointwise Q)] with ω hω
    exact hω.trans (add_le_add (inverse_bank_depth_response_baseline_cap M hg Q.1 m j r
      (hscale Q.1 Q.2).1 (hscale Q.1 Q.2).2) le_rfl)
  have hY : Measurable (bankFiniteRootResponseMax s M m J weights) :=
    history_finite_max_measurable _ _ (fun Q => ENNReal.continuous_ofReal.measurable.comp
      (root_inverse_response_measurable M m J weights Q.1))
  refine ⟨hY,history_finite_max_measurable _ _ hScaledMeas,?_,?_⟩
  · filter_upwards [ae_all_iff.mpr hSplit] with ω hω
    change (Finset.univ : Finset ↥s).sup (fun Q => ENNReal.ofReal
      (rootInverseResponse M Q.1 m J weights ω)) ≤ _
    apply Finset.sup_le
    intro Q hQ
    exact (hω Q).trans (add_le_add le_rfl (Finset.le_sup
      (f := fun Q : ↥s => bankRootScaledSelectedRemainder M Q.1 m (inverseBankRootRow r) ω) hQ))
  · have hh := bank_finite_max_L256 μ (Finset.univ : Finset ↥s)
      (fun Q : ↥s => bankRootScaledSelectedRemainder M Q.1 m (inverseBankRootRow r))
      hScaledMeas B (fun Q _ => hCap Q)
    have hh' : eLpNorm (bankFiniteRootRemainderMax s M m (inverseBankRootRow r)) 256 μ ≤
        (s.card:ℝ≥0∞)^(1/256:ℝ)*B := by
      change eLpNorm (historyFiniteMax (Finset.univ : Finset ↥s)
        (fun Q : ↥s => bankRootScaledSelectedRemainder M Q.1 m (inverseBankRootRow r))) 256 μ ≤ _
      simpa only [Finset.card_univ, Fintype.card_coe] using hh
    exact hh'.trans (bank_depth_population_budget r M s.card j hcard)

/-- The source D_j inverse-block maximum has its own nonnegative remainder
with the exact depth-j L128 reserve, without a history sum. -/
theorem inverse_bank_depth_block
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (r : InverseBankRow) (s : Finset (TriadicCube 2))
    (m J : ℤ) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1) (j : ℕ)
    (hscale : ∀ Q ∈ s, Q.scale ≤ m-(j:ℤ) ∧ (m-(j:ℤ))-Q.scale ≤ 5)
    (hcard : s.card ≤ 6*9^(45+j)) (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m (inverseBankRootRow r)) :
    InverseBankDepthBlockConclusion M r s m J weights j := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Y := bankFiniteRootResponseMax s M m J weights
  let R := bankFiniteRootRemainderMax s M m (inverseBankRootRow r)
  let y : Cutoff.CutoffSample 2 → ℝ := fun ω => (Y ω).toReal
  obtain ⟨hY,hR,hSplit,hR256⟩ := inverse_bank_depth_block_pretruncation M h hM hg r s
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
      0 ≤ inverseBankDepthBlockRemainder r s M m J weights j ω :=
    (positive_split (y ω) (inverseBankDepthA r M j) (inverseBankDepthSlack M j)).1
  have hRealSplit (ω : Cutoff.CutoffSample 2) : y ω ≤
      (inverseBankCap r:ℝ)*bankDepthFrame M j+inverseBankDepthBlockRemainder r s M m J weights j ω :=
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
