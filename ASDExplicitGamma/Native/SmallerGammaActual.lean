module

public import ASDExplicitGamma.Native.SmallerGamma
public import ASDExplicitGamma.Native.GenericSourceChildRows

/-! Actual-law continuation. The finite generic profiles and their complete
tails are compared before passing to endpoint caps. Earlier completed q1
outputs then discharge the refined-source inputs in the same true frame. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Inverse ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Cold ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- The corrected q1 endpoint is strictly below the carried refined-source
input. This is an exact rational comparison, without decimal rounding. -/
theorem native_source_q1_sharp_lt_carried :
    nativeBoundaryQ1Sharp < nativeQstar := by
  have heq : nativeBoundaryQ1Sharp = nativeEndpointQ1001Cap := by
    norm_num [nativeBoundaryQ1Sharp, nativeEndpointQ1001Cap]
  rw [heq]
  exact nativeEndpointQ1001_carried.1.trans nativeEndpointQ1001_carried.2

/-- Convert the actual positive extended q1 output into the real expectation
input of the refined source. Integrability and positivity are proved for the
actual observable before converting its expectation. -/
theorem native_source_q1_real_of_sharp
    (M : ABKModel 2) (m : ℤ)
    (hq1 : nativeCompletedSourceMean M m 1 ≤
      ENNReal.ofReal (theta M * (nativeBoundaryQ1Sharp : ℝ))) :
    (∫ ω, cutoffTraceDefect M m (m-1) ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ theta M * (nativeQstar : ℝ) := by
  have ht : 0 ≤ theta M :=
    div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hc : (nativeBoundaryQ1Sharp : ℝ) ≤ (nativeQstar : ℝ) := by
    exact_mod_cast native_source_q1_sharp_lt_carried.le
  have hbound := hq1.trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hc ht))
  simp only [nativeCompletedSourceMean, Nat.cast_one] at hbound
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_cutoffTraceDefect M m (m-1))
    (Filter.Eventually.of_forall (cutoffTraceDefect_nonneg M m (m-1)))] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg ht (by norm_num [nativeQstar]))).mp hbound

/-- Both complete generic rows, including the full tail allocation, have
degree one on the physical smaller-γ ray. The weights are compared positively
before the finite prefix and tail are combined. -/
theorem native_source_complete_rows_degree
    (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (r : Fin 6) :
    (nativeSourceGenericCompleteMeanRow M.gamma (theta M) r.val 1285 ≤
      theta M * nativeSourceGenericCompleteMeanRow (17/50000) 1 r.val 1285) ∧
    (nativeSourceGenericCompleteWeakRow M.gamma (theta M) r.val 1285 ≤
      theta M * nativeSourceGenericCompleteWeakRow (17/50000) 1 r.val 1285) := by
  exact ⟨native_source_generic_complete_mean_row_degree M.gamma (theta M) r.val 1285
      M.shellPrefix.gamma_pos.le hg rfl (by omega) (by norm_num),
    native_source_generic_complete_weak_row_degree M.gamma (theta M) r.val 1285
      M.shellPrefix.gamma_pos.le hg rfl (by omega) (by norm_num)⟩

/-- The exact bundled generic/refined producer conclusion follows from the
actual mean and complete weak-row theorems, with only the exact earlier-q1
producer outputs still supplied separately. No generic row, Lp cap, or tail
estimate is a hypothesis. -/
theorem native_source_generic_continuation_of_q1
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k)
    (hq1 : ∀ k < m, nativeCompletedSourceMean M k 1 ≤
      ENNReal.ofReal (theta M * (nativeBoundaryQ1Sharp : ℝ))) :
    NativeGenericSourceRowsConclusion M m := by
  have hq1real : ∀ k < m, (∫ ω, cutoffTraceDefect M k (k-1) ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ theta M * (nativeQstar : ℝ) :=
    fun k hk => native_source_q1_real_of_sharp M k (hq1 k hk)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro depth hdepth
    have hdegree := native_source_generic_mean_profile_degree M.gamma (theta M)
      (9+depth) M.shellPrefix.gamma_pos.le hg rfl hdepth
    exact (native_source_depth_generic_mean_ennreal M h hM hg m hpast depth hdepth).trans
      (ENNReal.ofReal_le_ofReal hdegree)
  · intro r
    have hrows := native_source_complete_rows_degree M hg r
    have hdegree := native_source_weak_inverse_charge_degree (theta M) _ _ _ _
      hrows.1 hrows.2
    exact (native_source_generic_weak_actual M h hM hg m hpast r.val (by omega)).trans
      (ENNReal.ofReal_le_ofReal hdegree)
  · intro r
    exact native_source_child_mean_rows_of_q1 M h hM hg m hpast r hq1real
  · intro r
    exact native_source_child_weak_rows_of_q1 M h hM hg m hpast r hq1real

/-- The exact endpoint mean is the minimum of the refined old mean and the
boundary-fixed parent entry, including the ordinary mean at depth zero. -/
theorem native_source_mean_endpoint_min (r : Fin 6) :
    ((nativeCompletedMeanRows.getD r.val 0 : ℚ) : ℝ) =
      min (nativeCompletedPrefixOldMean r : ℝ)
        ((nativeBoundaryParentCaps.getD r.val 0 : ℚ) : ℝ) := by
  have hh := congrArg Prod.fst (native_completed_prefix_endpoint_result r)
  change min (nativeCompletedPrefixOldMean r)
    (nativeCompletedPrefixParents.getD r.val 0) = nativeCompletedMeanRows.getD r.val 0 at hh
  have hc := congrArg (fun q : ℚ => (q : ℝ)) hh
  rw [Rat.cast_min, nativeCompletedPrefixParents,
    ← nativeBoundaryParentCaps_source.1] at hc
  exact hc.symm

/-- Prove the six completed mean rows by comparing two bounds for the same
actual completed-law observable. At depth zero the parent input is exactly
the stable ordinary-mean hypothesis; the other five inputs are actual parent
producer outputs. No completed mean-row cap is assumed. -/
theorem native_source_mean_prefix_continuation
    (M : ABKModel 2) (m : ℤ)
    (hmean : ordinaryMean M m ≤ ENNReal.ofReal ((3/50:ℝ)*theta M))
    (hgeneric : NativeGenericSourceRowsConclusion M m)
    (hparent : ∀ j : Fin 16, nativeCompletedSourceMean M m (j.val+1) ≤
      ENNReal.ofReal
        (theta M * ((nativeBoundaryParentCaps.getD (j.val+1) 0 : ℚ) : ℝ))) :
    ∀ r : Fin 6, nativeCompletedSourceMean M m r.val ≤
      ENNReal.ofReal (theta M * ((nativeCompletedMeanRows.getD r.val 0 : ℚ) : ℝ)) := by
  intro r
  have hold := hgeneric.2.2.1 r
  have hpar : nativeCompletedSourceMean M m r.val ≤
      ENNReal.ofReal (theta M * ((nativeBoundaryParentCaps.getD r.val 0 : ℚ) : ℝ)) := by
    rcases Nat.eq_zero_or_pos r.val with hr | hr
    · simpa [hr, native_completed_source_mean_zero, nativeBoundaryParentCaps,
        nativeA, mul_comm] using hmean
    · let j : Fin 16 := ⟨r.val-1, by omega⟩
      have hj : j.val+1 = r.val := by dsimp [j]; omega
      simpa only [hj] using hparent j
  rw [native_source_mean_endpoint_min]
  rcases le_total (nativeCompletedPrefixOldMean r : ℝ)
      ((nativeBoundaryParentCaps.getD r.val 0 : ℚ) : ℝ) with hh | hh
  · rw [min_eq_left hh]
    exact hold
  · rw [min_eq_right hh]
    exact hpar

end
end ASDExplicitGamma.Native
