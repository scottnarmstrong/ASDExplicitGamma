module

public import ASDExplicitGamma.Native.GenericSourceWeightedActual
public import ASDExplicitGamma.Native.GenericSourcePhysicalWeights

/-! The complete actual-law baseline-plus-marginal-rare weak row. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Combine actual weighted mean and L20 caps into the exact carried weak
charge. This is the marginal source row, before the mixed maximum reserve. -/
theorem native_source_weak_charge_of_weighted_caps
    (M : ABKModel 2) (m : ℤ) (r : ℕ) (hg : M.gamma ≤ gammaZero)
    (W V : ℝ) (hW0 : 0 ≤ W) (hV0 : 0 ≤ V)
    (hW : (∑' j : ℕ, ENNReal.ofReal ((nativeSourceHistoryWeight M.gamma)^j)*
      nativeCompletedSourceMean M m (r+j)) ≤ ENNReal.ofReal W)
    (hV : (∑' j : ℕ, ENNReal.ofReal ((nativeSourceHistoryWeight M.gamma)^j)*
      eLpNorm (cutoffTraceDefect M m (m-((r+j:ℕ):ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal V) :
    nativeCompletedSourceWeak M m r ≤ ENNReal.ofReal (nativeSourceWeakInverseCharge W V) := by
  let U := fun j => nativeCompletedSourceMean M m (r+j)
  let Z := fun j => eLpNorm (cutoffTraceDefect M m (m-((r+j:ℕ):ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure
  let q := nativeSourceHistoryWeight M.gamma
  let b := ENNReal.ofReal (3683/2500:ℝ)
  let epsilon := ENNReal.ofReal (3/10^46:ℝ)
  have hw := native_source_physical_weights M.gamma M.shellPrefix.gamma_pos.le hg
  have hsum : (∑' j : ℕ, ENNReal.ofReal (Scalar.inverseHistoryDiscount^(2*j)*(3:ℝ)^(2*M.gamma*(j:ℝ)))*
      (b*U j+epsilon*Z j)) ≤ b*ENNReal.ofReal W+epsilon*ENNReal.ofReal V := by
    calc
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (q^j)*(b*U j+epsilon*Z j) :=
        ENNReal.tsum_le_tsum (fun j => mul_le_mul' (ENNReal.ofReal_le_ofReal (hw.2.2 j)) le_rfl)
      _ = b*(∑' j : ℕ, ENNReal.ofReal (q^j)*U j)+
          epsilon*(∑' j : ℕ, ENNReal.ofReal (q^j)*Z j) := by
        have hterm (j : ℕ) : ENNReal.ofReal (q^j)*(b*U j+epsilon*Z j)=
            b*(ENNReal.ofReal (q^j)*U j)+epsilon*(ENNReal.ofReal (q^j)*Z j) := by ring
        simp_rw [hterm]
        rw [ENNReal.tsum_add,ENNReal.tsum_mul_left,ENNReal.tsum_mul_left]
      _ ≤ _ := add_le_add (mul_le_mul' le_rfl hW) (mul_le_mul' le_rfl hV)
  have hnorm : ENNReal.ofReal (1-Scalar.inverseHistoryDiscount^2) ≤
      ENNReal.ofReal (1-nativeSourceAlphaMinus^2) := ENNReal.ofReal_le_ofReal hw.2.1
  have hh := mul_le_mul' hnorm hsum
  change nativeCompletedSourceWeak M m r ≤ _ at hh
  convert hh using 1
  dsimp [nativeSourceWeakInverseCharge,nativeSourceB128,b,epsilon]
  rw [ENNReal.ofReal_mul (by norm_num [nativeSourceAlphaMinus] : (0:ℝ)≤1-nativeSourceAlphaMinus^2),
    ENNReal.ofReal_add (mul_nonneg (by norm_num) hW0) (mul_nonneg (by positivity) hV0),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3683/2500),ENNReal.ofReal_mul (by positivity : (0:ℝ)≤3/10^46)]

/-- Both complete generic rows are nonnegative, with their explicit tails. -/
theorem native_source_generic_actual_complete_rows_nonneg
    (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (r : ℕ) (hr : r ≤ 5) :
    0 ≤ nativeSourceGenericCompleteMeanRow M.gamma (theta M) r 1285 ∧
    0 ≤ nativeSourceGenericCompleteWeakRow M.gamma (theta M) r 1285 := by
  have hg0 := M.shellPrefix.gamma_pos.le
  have ht0 : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  have hq0 := (native_source_history_weight_endpoint_and_ratio M.gamma hg0 hg).1
  have htail : 0 ≤ nativeSourceGenericTailCharge M.gamma (theta M) r 1285 := by
    exact mul_nonneg (native_source_generic_raw_frame_nonneg M.gamma (theta M) (9+r) hg0 ht0 hg (by omega))
      (by unfold nativeSourceGenericTailFactor; positivity)
  constructor
  · apply add_nonneg _ htail
    apply Finset.sum_nonneg
    intro j hj
    have hjN := Finset.mem_range.mp hj
    exact mul_nonneg (pow_nonneg hq0 j)
      (native_source_generic_mean_profile_nonneg M.gamma (theta M) (9+r+j) hg0 ht0 hg (by omega))
  · apply add_nonneg _ htail
    apply Finset.sum_nonneg
    intro j hj
    have hjN := Finset.mem_range.mp hj
    exact mul_nonneg (pow_nonneg hq0 j)
      (native_source_generic_weak_frame_profile_nonneg M.gamma (theta M) (9+r+j) hg0 ht0 hg (by omega))

/-- The actual complete generic weak charge at each source offset obeys
exactly the finite bound, including all marginal rare and unbounded raw tail terms. -/
theorem native_source_generic_weak_actual
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (r : ℕ) (hr : r ≤ 5) :
    nativeCompletedSourceWeak M m r ≤ ENNReal.ofReal (nativeSourceWeakInverseCharge
      (nativeSourceGenericCompleteMeanRow M.gamma (theta M) r 1285)
      (nativeSourceGenericCompleteWeakRow M.gamma (theta M) r 1285)) := by
  have hpos := native_source_generic_actual_complete_rows_nonneg M hg r hr
  exact native_source_weak_charge_of_weighted_caps M m r hg _ _ hpos.1 hpos.2
    (native_source_generic_weighted_mean_actual M h hM hg m hpast r hr)
    (native_source_generic_weighted_norm_actual M h hM hg m hpast r hr)

end
end ASDExplicitGamma.Native
