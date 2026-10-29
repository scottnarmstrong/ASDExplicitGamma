module

public import ASDExplicitGamma.Native.SmallerGammaActual
public import ASDExplicitGamma.Native.SmallerGammaWeakData

/-! Positive actual-law completed-prefix continuation. The boundary-fixed
parent and refined bounds apply to the same completed observable. Their
minimum controls the finite head; complete mean and rare-trace tails are
then added before the exact endpoint comparison. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Inverse ASDExplicitGamma.Numerics.Native
open scoped ENNReal
noncomputable section

/-- Extend the exact parent producer by the named ordinary-mean input at
depth zero. Every depth uses cutoff m and its single completed true frame. -/
theorem native_source_parent_with_zero
    (M : ABKModel 2) (m : ℤ)
    (hmean : ordinaryMean M m ≤ ENNReal.ofReal ((3/50:ℝ)*theta M))
    (hparent : ∀ j : Fin 16, nativeCompletedSourceMean M m (j.val+1) ≤
      ENNReal.ofReal
        (theta M * ((nativeBoundaryParentCaps.getD (j.val+1) 0 : ℚ) : ℝ)))
    (d : Fin 17) : nativeCompletedSourceMean M m d.val ≤
      ENNReal.ofReal (theta M * ((nativeBoundaryParentCaps.getD d.val 0 : ℚ) : ℝ)) := by
  rcases Nat.eq_zero_or_pos d.val with hd | hd
  · simpa [hd, native_completed_source_mean_zero, nativeBoundaryParentCaps,
      nativeA, mul_comm] using hmean
  · let j : Fin 16 := ⟨d.val-1, by omega⟩
    have hj : j.val+1 = d.val := by dsimp [j]; omega
    simpa only [hj] using hparent j

/-- Each actual finite mean meets the positive endpoint minimum. The refined
input reads q1 strictly before m, and the parent input concerns the very same
cutoff and true-frame observable. -/
theorem native_source_completed_finite_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k)
    (hmean : ordinaryMean M m ≤ ENNReal.ofReal ((3/50:ℝ)*theta M))
    (hq1 : ∀ k < m, nativeCompletedSourceMean M k 1 ≤
      ENNReal.ofReal (theta M * (nativeBoundaryQ1Sharp : ℝ)))
    (hparent : ∀ j : Fin 16, nativeCompletedSourceMean M m (j.val+1) ≤
      ENNReal.ofReal
        (theta M * ((nativeBoundaryParentCaps.getD (j.val+1) 0 : ℚ) : ℝ)))
    (d : Fin 56) : nativeCompletedSourceMean M m d.val ≤
      ENNReal.ofReal (theta M * (nativeSourceCompletedHeadMean d : ℝ)) := by
  have hk : m-((9+d.val:ℕ):ℤ) < m := by omega
  have hchild := native_source_depth_child_mean_ennreal_of_q1 M h hM hg m hpast d
    (native_source_q1_real_of_sharp M _ (hq1 _ hk))
  unfold nativeSourceCompletedHeadMean
  split_ifs with hd
  · have hpar := native_source_parent_with_zero M m hmean hparent ⟨d.val, hd⟩
    rcases le_total (nativeSourceChildRationalWitness d)
        (nativeBoundaryParentCaps.getD d.val 0) with hh | hh
    · rw [min_eq_left hh]
      exact hchild
    · rw [min_eq_right hh]
      exact hpar
  · exact hchild

private theorem completedWeightedHead_nonneg (r : Fin 6) :
    0 ≤ (nativeSourceCompletedWeightedHead r : ℝ) := by
  rw [nativeSourceCompletedWeightedHead, Rat.cast_sum]
  apply Finset.sum_nonneg
  intro j _
  rw [Rat.cast_mul, Rat.cast_pow]
  exact mul_nonneg (pow_nonneg (by norm_num [nativeE, nativeGamma]) _)
    ((Rat.cast_nonneg (K := ℝ)).mpr (native_source_completed_head_nonneg _))

/-- The complete positive weighted mean series uses all finite refined
depths, the corrected parent minima at depths ≤16, and the entire post-gap-64
mean tail. No bound on the completed weak row is a premise. -/
theorem native_source_completed_weighted_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k)
    (hmean : ordinaryMean M m ≤ ENNReal.ofReal ((3/50:ℝ)*theta M))
    (hq1 : ∀ k < m, nativeCompletedSourceMean M k 1 ≤
      ENNReal.ofReal (theta M * (nativeBoundaryQ1Sharp : ℝ)))
    (hparent : ∀ j : Fin 16, nativeCompletedSourceMean M m (j.val+1) ≤
      ENNReal.ofReal
        (theta M * ((nativeBoundaryParentCaps.getD (j.val+1) 0 : ℚ) : ℝ)))
    (r : Fin 6) :
    (∑' j : ℕ, ENNReal.ofReal (nativeSourceHistoryWeight M.gamma^j) *
      nativeCompletedSourceMean M m (r.val+j)) ≤
      ENNReal.ofReal (theta M * ((nativeSourceCompletedWeightedHead r : ℝ)+1/100000)) := by
  let q := nativeSourceHistoryWeight M.gamma
  let U := fun j => nativeCompletedSourceMean M m (r.val+j)
  let J := 56-r.val
  have ht : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hw := native_source_history_weight_endpoint_and_ratio M.gamma M.shellPrefix.gamma_pos.le hg
  have hq : 0 ≤ q := hw.1
  have hhead0 := completedWeightedHead_nonneg r
  have hhead : (∑ j ∈ Finset.range J, ENNReal.ofReal (q^j)*U j) ≤
      ENNReal.ofReal (theta M*(nativeSourceCompletedWeightedHead r : ℝ)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    calc
      _ ≤ ∑ j : Fin J, ENNReal.ofReal
          (theta M*((nativeSourceRationalHistoryWeight : ℝ)^j.val *
            (nativeSourceCompletedHeadMean ⟨r.val+j.val, by dsimp [J] at j; omega⟩ : ℝ))) := by
        apply Finset.sum_le_sum
        intro j _
        have hj : r.val+j.val < 56 := by have := j.isLt; dsimp [J] at this; omega
        have hc := native_source_completed_finite_mean M h hM hg m hpast
          hmean hq1 hparent ⟨r.val+j.val, hj⟩
        have hp := pow_le_pow_left₀ hq hw.2.1 j.val
        rw [← native_source_rational_history_weight_cast] at hp
        have hh := mul_le_mul' (ENNReal.ofReal_le_ofReal hp) hc
        convert hh using 1
        rw [← ENNReal.ofReal_mul
          (pow_nonneg (by norm_num [nativeSourceRationalHistoryWeight, nativeE, nativeGamma]) _)]
        congr 1
        ring
      _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · congr 1
          rw [nativeSourceCompletedWeightedHead, Rat.cast_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          simp only [nativeSourceRationalHistoryWeight, Rat.cast_mul, Rat.cast_pow]
        · intro j _
          exact mul_nonneg ht (mul_nonneg
            (pow_nonneg (by norm_num [nativeSourceRationalHistoryWeight, nativeE, nativeGamma]) _)
            ((Rat.cast_nonneg (K := ℝ)).mpr (native_source_completed_head_nonneg _)))
  have htail := native_source_complete_mean_tail_aux M h hM hg m hpast r
  have hs : Summable (fun j : ℕ => ENNReal.ofReal (q^(j+J))*U (j+J)) := ENNReal.summable
  rw [← hs.sum_add_tsum_nat_add' (f := fun j : ℕ => ENNReal.ofReal (q^j)*U j) (k := J)]
  have htail' : (∑' j : ℕ, ENNReal.ofReal (q^(j+J))*U (j+J)) ≤
      ENNReal.ofReal (theta M*(1/100000 : ℝ)) := by
    simpa only [q, U, J, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail
  have hh := add_le_add hhead htail'
  rw [← ENNReal.ofReal_add (mul_nonneg ht hhead0) (by positivity)] at hh
  simpa only [mul_add] using hh

/-- The complete actual weak charge meets the exact endpoint, including
the marginal rare L20 payment and every depth. This uses a positive minimum
before summing; it never subtracts two estimates of the actual law. -/
theorem native_source_completed_weak_continuation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k)
    (hmean : ordinaryMean M m ≤ ENNReal.ofReal ((3/50:ℝ)*theta M))
    (hq1 : ∀ k < m, nativeCompletedSourceMean M k 1 ≤
      ENNReal.ofReal (theta M * (nativeBoundaryQ1Sharp : ℝ)))
    (hparent : ∀ j : Fin 16, nativeCompletedSourceMean M m (j.val+1) ≤
      ENNReal.ofReal
        (theta M * ((nativeBoundaryParentCaps.getD (j.val+1) 0 : ℚ) : ℝ)))
    (r : Fin 6) : nativeCompletedSourceWeak M m r.val ≤
      ENNReal.ofReal (theta M * ((nativeCompletedWeakRows.getD r.val 0 : ℚ) : ℝ)) := by
  have ht : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hhead := completedWeightedHead_nonneg r
  have hh := native_source_weak_charge_of_weighted_caps M m r.val hg
    (theta M*((nativeSourceCompletedWeightedHead r : ℝ)+1/100000))
    (theta M*(10^12 : ℝ)) (mul_nonneg ht (by positivity)) (by positivity)
    (native_source_completed_weighted_mean M h hM hg m hpast hmean hq1 hparent r)
    (native_source_complete_trace_companion_aux M h hM hg m hpast r)
  apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
  have hc := mul_le_mul_of_nonneg_left ((Rat.cast_le (K := ℝ)).mpr
    (native_source_completed_weak_endpoint r)) ht
  norm_num only [Rat.cast_mul, Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_pow,
    Rat.cast_ofNat, nativeB, nativeEps] at hc
  convert hc using 1
  dsimp [nativeSourceWeakInverseCharge, nativeSourceB128, nativeSourceAlphaMinus]
  ring

/-- The stable smaller-γ conclusion from exact q1 and boundary-fixed parent
producer outputs. The generic/refined rows, completed means, complete weak
series, rare companion and exact endpoint comparisons are proved internally;
no completed-prefix cap or generic-row result is assumed. -/
theorem native_source_smaller_gamma_of_q1_parent
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k)
    (hmean : ordinaryMean M m ≤ ENNReal.ofReal ((3/50:ℝ)*theta M))
    (hq1 : ∀ k ≤ m, nativeCompletedSourceMean M k 1 ≤
      ENNReal.ofReal (theta M * (nativeBoundaryQ1Sharp : ℝ)))
    (hparent : ∀ j : Fin 16, nativeCompletedSourceMean M m (j.val+1) ≤
      ENNReal.ofReal
        (theta M * ((nativeBoundaryParentCaps.getD (j.val+1) 0 : ℚ) : ℝ))) :
    NativeSourceSmallerGammaBounds M m := by
  have hqold := fun k (hk : k < m) => hq1 k hk.le
  have hgeneric := native_source_generic_continuation_of_q1 M h hM hg m hpast hqold
  exact ⟨hq1 m le_rfl, hparent,
    native_source_mean_prefix_continuation M m hmean hgeneric hparent,
    native_source_completed_weak_continuation M h hM hg m hpast hmean hqold hparent⟩

end
end ASDExplicitGamma.Native
