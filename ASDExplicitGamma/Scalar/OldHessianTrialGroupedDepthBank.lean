module

public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedBank
public import ASDExplicitGamma.Inverse.BankLocal

/-! The OLD local depth bank on the actual scalar parent. The 9^89 grouping
is applied only to each depth's rare remainder, preserving the local baseline. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Inverse Algsuperdiff.Section3
open scoped ENNReal
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Actual grouped inverse-block maximum at additional weak depth j. -/
def oldHessianGroupedDepthBlocks (M : ABKModel 2) (m : ℤ) (j : ℕ) :
    Cutoff.CutoffSample 2 → ℝ≥0∞ :=
  historyFiniteMax (oldHessianMacroCells m) (fun Q =>
    bankFiniteRootResponseMax (bankObserverDepthRootUnion Q 5 j) M m (m+40)
      (bankPartialInsertionWeights m 1 0))

/-- Grouped OLD local depth remainder; no ordinary baseline is multiplied. -/
def oldHessianGroupedDepthRare (M : ABKModel 2) (m : ℤ) (j : ℕ) :
    Cutoff.CutoffSample 2 → ℝ≥0∞ :=
  historyFiniteMax (oldHessianMacroCells m) (fun Q ω => ENNReal.ofReal
    (inverseBankDepthBlockRemainder .localInverse (bankObserverDepthRootUnion Q 5 j)
      M m (m+40) (bankPartialInsertionWeights m 1 0) j ω))

/-- The grouped actual depth maximum is finite a.e. and retains the exact
local bank split. All estimates are supplied by the causal bank producers. -/
theorem old_hessian_grouped_local_depth_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ k<N,nativeInductionState M h k) (m : ℤ) (hm : m<N) (j : ℕ) :
    Measurable (oldHessianGroupedDepthRare M m j) ∧
    eLpNorm (oldHessianGroupedDepthRare M m j) 128
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (5*inverseBankDepthReserve .localInverse M j) ∧
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      oldHessianGroupedDepthBlocks M m j ω<⊤ ∧
      oldHessianGroupedDepthBlocks M m j ω ≤
        ENNReal.ofReal ((inverseBankCap .localInverse:ℝ)*bankDepthFrame M j)+
          oldHessianGroupedDepthRare M m j ω := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let I := oldHessianMacroCells m
  let R := fun Q => inverseBankDepthBlockRemainder .localInverse
    (bankObserverDepthRootUnion Q 5 j) M m (m+40) (bankPartialInsertionWeights m 1 0) j
  have hstates : ∀ k<m,nativeInductionState M h k := fun k hk => hpast k (hk.trans hm)
  have hbank (Q : TriadicCube 2) (hQ : Q∈I) :
      InverseBankDepthBlockConclusion M .localInverse (bankObserverDepthRootUnion Q 5 j)
        m (m+40) (bankPartialInsertionWeights m 1 0) j :=
    ((local_inverse_bank_attenuated_of_states M h hM hg Q m
      ((old_hessian_macrocell_geometry m).2 Q hQ).1 5 le_rfl 0 (by norm_num) hstates).2 j).2
  have hRm (Q : TriadicCube 2) : Measurable (R Q) := by
    let Y := bankFiniteRootResponseMax (bankObserverDepthRootUnion Q 5 j) M m (m+40)
      (bankPartialInsertionWeights m 1 0)
    have hYm : Measurable Y := history_finite_max_measurable _ _ (fun U =>
      ENNReal.continuous_ofReal.measurable.comp
        (root_inverse_response_measurable M m (m+40) (bankPartialInsertionWeights m 1 0) U.val))
    exact measurable_const.max (((ENNReal.measurable_toReal.comp hYm).sub_const
      (inverseBankDepthA .localInverse M j)).sub_const (inverseBankDepthSlack M j))
  have hRareMeas : Measurable (oldHessianGroupedDepthRare M m j) :=
    history_finite_max_measurable _ _ (fun Q =>
      ENNReal.continuous_ofReal.measurable.comp (hRm Q))
  have hPop := positive_finite_max_L128 μ I (fun Q ω => ENNReal.ofReal (R Q ω))
    (fun Q => ENNReal.continuous_ofReal.measurable.comp (hRm Q))
    (ENNReal.ofReal (inverseBankDepthReserve .localInverse M j)) (fun Q hQ => by
      change eLpNorm (ENNReal.ofReal ∘ R Q) 128 μ ≤ _
      rw [eLpNorm_ofReal (R Q) (Filter.Eventually.of_forall ((hbank Q hQ).remainder_nonneg))]
      exact (hbank Q hQ).remainder_L128)
  refine ⟨hRareMeas,?_,?_⟩
  · calc
      _ ≤ (I.card:ℝ≥0∞)^(1/128:ℝ)*ENNReal.ofReal (inverseBankDepthReserve .localInverse M j) := hPop
      _ ≤ 5*ENNReal.ofReal (inverseBankDepthReserve .localInverse M j) :=
        mul_le_mul_of_nonneg_right
          (bank_scalar_grouping_payment I.card (old_hessian_macrocell_geometry m).1.le) bot_le
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5)]; norm_num
  · have hall : ∀ᵐ ω ∂μ,∀ Q : ↥I,
        bankFiniteRootResponseMax (bankObserverDepthRootUnion Q.val 5 j) M m (m+40)
          (bankPartialInsertionWeights m 1 0) ω<⊤ ∧
        bankFiniteRootResponseMax (bankObserverDepthRootUnion Q.val 5 j) M m (m+40)
          (bankPartialInsertionWeights m 1 0) ω ≤
          ENNReal.ofReal ((inverseBankCap .localInverse:ℝ)*bankDepthFrame M j)+ENNReal.ofReal (R Q.val ω) :=
      Filter.eventually_all.mpr (fun Q => (hbank Q.val Q.property).block_finite.and
        (hbank Q.val Q.property).block_le)
    filter_upwards [hall] with ω hω
    constructor
    · exact (Finset.sup_lt_iff (by simp : (⊥:ℝ≥0∞)<⊤)).mpr (fun Q hQ => (hω ⟨Q,hQ⟩).1)
    · apply Finset.sup_le
      intro Q hQ
      exact (hω ⟨Q,hQ⟩).2.trans (add_le_add le_rfl
        (Finset.le_sup (f := fun Q => ENNReal.ofReal (R Q ω)) hQ))

end
end ASDExplicitGamma.Scalar
