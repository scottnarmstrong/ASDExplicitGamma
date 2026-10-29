module

public import ASDExplicitGamma.Native.GenericSourceChildDepth
public import ASDExplicitGamma.Native.GenericSourceShortTailActual
public import ASDExplicitGamma.Native.GenericSourceWeakActual

/-! Complete refined OLD source rows from the separate, earlier q1 result.
The explicit q1 input is not discharged by the generic source estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Numerics.Native
open scoped ENNReal
noncomputable section

/-- Every finite refined witness is positive. -/
theorem native_source_child_rational_witness_nonneg (i : Fin 56) :
    0 ≤ nativeSourceChildRationalWitness i := by
  fin_cases i <;> decide +kernel

/-- Nonnegativity of the rational finite weighted head. -/
theorem native_source_child_rational_weighted_head_nonneg (r : Fin 6) :
    0 ≤ (nativeSourceChildRationalWeightedHead r:ℝ) := by
  rw [nativeSourceChildRationalWeightedHead,Rat.cast_sum]
  apply Finset.sum_nonneg
  intro j _
  rw [Rat.cast_mul,Rat.cast_pow]
  exact mul_nonneg (pow_nonneg (by norm_num [nativeE,nativeGamma]) _)
    ((Rat.cast_nonneg (K := ℝ)).mpr (native_source_child_rational_witness_nonneg _))

/-- The entire weighted refined mean series, including all depths beyond
its finite head, follows from the completed q1 input at earlier cutoffs. -/
theorem native_source_child_weighted_mean_of_q1
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (r : Fin 6)
    (hq1 : ∀ k < m, (∫ ω, cutoffTraceDefect M k (k-1) ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ theta M*(nativeQstar:ℝ)) :
    (∑' j : ℕ, ENNReal.ofReal (nativeSourceHistoryWeight M.gamma^j)*
      nativeCompletedSourceMean M m (r.val+j)) ≤
      ENNReal.ofReal (theta M*((nativeSourceChildRationalWeightedHead r:ℝ)+1/100000)) := by
  let q := nativeSourceHistoryWeight M.gamma
  let U := fun j => nativeCompletedSourceMean M m (r.val+j)
  let J := 56-r.val
  have ht : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hw := native_source_history_weight_endpoint_and_ratio M.gamma M.shellPrefix.gamma_pos.le hg
  have hq : 0 ≤ q := hw.1
  have hhead0 := native_source_child_rational_weighted_head_nonneg r
  have hhead : (∑ j ∈ Finset.range J, ENNReal.ofReal (q^j)*U j) ≤
      ENNReal.ofReal (theta M*(nativeSourceChildRationalWeightedHead r:ℝ)) := by
    rw [←Fin.sum_univ_eq_sum_range]
    calc
      _ ≤ ∑ j : Fin J, ENNReal.ofReal
          (theta M*((nativeSourceRationalHistoryWeight:ℝ)^j.val*
            (nativeSourceChildRationalWitness ⟨r.val+j.val,by dsimp [J] at j; omega⟩:ℝ))) := by
        apply Finset.sum_le_sum
        intro j _
        have hj : r.val+j.val<56 := by have := j.isLt; dsimp [J] at this; omega
        have hk : m-((9+(r.val+j.val):ℕ):ℤ)<m := by omega
        have hc := native_source_depth_child_mean_ennreal_of_q1 M h hM hg m hpast
          ⟨r.val+j.val,hj⟩ (hq1 _ hk)
        have hp := pow_le_pow_left₀ hq hw.2.1 j.val
        rw [←native_source_rational_history_weight_cast] at hp
        have hh := mul_le_mul' (ENNReal.ofReal_le_ofReal hp) hc
        convert hh using 1
        rw [←ENNReal.ofReal_mul (pow_nonneg (by norm_num [nativeSourceRationalHistoryWeight,nativeE,nativeGamma]) _)]
        congr 1
        ring
      _ = _ := by
        rw [←ENNReal.ofReal_sum_of_nonneg]
        · congr 1
          rw [nativeSourceChildRationalWeightedHead,Rat.cast_sum,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          simp only [nativeSourceRationalHistoryWeight,Rat.cast_mul,Rat.cast_pow]
        · intro j _
          exact mul_nonneg ht (mul_nonneg
            (pow_nonneg (by norm_num [nativeSourceRationalHistoryWeight,nativeE,nativeGamma]) _)
            ((Rat.cast_nonneg (K := ℝ)).mpr (native_source_child_rational_witness_nonneg _)))
  have htail := native_source_complete_mean_tail_aux M h hM hg m hpast r
  have hs : Summable (fun j : ℕ => ENNReal.ofReal (q^(j+J))*U (j+J)) := ENNReal.summable
  rw [←hs.sum_add_tsum_nat_add' (f := fun j : ℕ => ENNReal.ofReal (q^j)*U j) (k := J)]
  have htail' : (∑' j : ℕ, ENNReal.ofReal (q^(j+J))*U (j+J)) ≤
      ENNReal.ofReal (theta M*(1/100000:ℝ)) := by
    simpa only [q,U,J,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using htail
  have hh := add_le_add hhead htail'
  rw [←ENNReal.ofReal_add (mul_nonneg ht hhead0) (by positivity)] at hh
  simpa only [mul_add] using hh

/-- The completed refined OLD root means meet the six recorded inputs. -/
theorem native_source_child_mean_rows_of_q1
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (r : Fin 6)
    (hq1 : ∀ k < m, (∫ ω, cutoffTraceDefect M k (k-1) ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ theta M*(nativeQstar:ℝ)) :
    nativeCompletedSourceMean M m r.val ≤
      ENNReal.ofReal (theta M*(nativeCompletedPrefixOldMean r:ℝ)) := by
  have hk : m-((9+r.val:ℕ):ℤ)<m := by omega
  exact (native_source_depth_child_mean_ennreal_of_q1 M h hM hg m hpast
    ⟨r.val,by omega⟩ (hq1 _ hk)).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left ((Rat.cast_le (K := ℝ)).mpr
      (native_source_child_rational_mean_bound r))
      (div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero]))))

/-- All six refined OLD weak source rows include the complete mean tail
and the complete L20 rare companion. The only separate producer input is q1. -/
theorem native_source_child_weak_rows_of_q1
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (r : Fin 6)
    (hq1 : ∀ k < m, (∫ ω, cutoffTraceDefect M k (k-1) ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ theta M*(nativeQstar:ℝ)) :
    nativeCompletedSourceWeak M m r.val ≤
      ENNReal.ofReal (theta M*(nativeCompletedPrefixOldXi r:ℝ)) := by
  have ht : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hhead := native_source_child_rational_weighted_head_nonneg r
  have hh := native_source_weak_charge_of_weighted_caps M m r.val hg
    (theta M*((nativeSourceChildRationalWeightedHead r:ℝ)+1/100000))
    (theta M*(10^12:ℝ)) (mul_nonneg ht (by positivity)) (by positivity)
    (native_source_child_weighted_mean_of_q1 M h hM hg m hpast r hq1)
    (native_source_complete_trace_companion_aux M h hM hg m hpast r)
  apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
  have hc := mul_le_mul_of_nonneg_left ((Rat.cast_le (K := ℝ)).mpr
    (native_source_child_rational_weak_bound r)) ht
  norm_num only [Rat.cast_mul,Rat.cast_add,Rat.cast_sub,Rat.cast_div,Rat.cast_pow,
    Rat.cast_ofNat,nativeB,nativeEps] at hc
  convert hc using 1
  dsimp [nativeSourceWeakInverseCharge,nativeSourceB128,nativeSourceAlphaMinus]
  ring

end
end ASDExplicitGamma.Native
