module

public import ASDExplicitGamma.Native.GenericSourceSeriesEnvelope

/-! Completed-law weighted source rows with their entire positive tails. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The complete actual mean sum obeys the literal finite scalar source
row plus its full tail allocation. All cutoffs are strictly below m. -/
theorem native_source_generic_weighted_mean_actual
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (r : ℕ) (hr : r ≤ 5) :
    (∑' j : ℕ, ENNReal.ofReal ((nativeSourceHistoryWeight M.gamma)^j)*
      nativeCompletedSourceMean M m (r+j)) ≤
      ENNReal.ofReal (nativeSourceGenericCompleteMeanRow M.gamma (theta M) r 1285) := by
  have hg0 := M.shellPrefix.gamma_pos.le
  have ht0 : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  have he := native_source_extended_series_envelope M hg r 1285
    (fun j => nativeCompletedSourceMean M m (r+j))
    (fun j => nativeSourceGenericMeanProfile M.gamma (theta M) (9+r+j))
    (fun j hj => native_source_generic_mean_profile_nonneg M.gamma (theta M) (9+r+j)
      hg0 ht0 hg (by omega))
    (fun j hj => by simpa only [Nat.add_assoc] using
      native_source_depth_generic_mean_ennreal M h hM hg m hpast (r+j) (by omega))
    (fun j _ => by simpa only [Nat.add_assoc] using
      native_source_depth_exponential_mean_ennreal M h hM hg m hpast (r+j))
  exact he.trans (ENNReal.ofReal_le_ofReal
    (native_source_generic_complete_mean_row_covers_exponential_tail M.gamma (theta M) r 1285
      hg0 hg ht0 hr (by norm_num)))

/-- The actual L20 rare-trace sum obeys the full finite source frame row and
its complete unbounded-depth tail. No real tsum can hide divergence. -/
theorem native_source_generic_weighted_norm_actual
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (r : ℕ) (hr : r ≤ 5) :
    (∑' j : ℕ, ENNReal.ofReal ((nativeSourceHistoryWeight M.gamma)^j)*
      eLpNorm (cutoffTraceDefect M m (m-((r+j:ℕ):ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (nativeSourceGenericCompleteWeakRow M.gamma (theta M) r 1285) := by
  have hg0 := M.shellPrefix.gamma_pos.le
  have ht0 : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  have he := native_source_extended_series_envelope M hg r 1285
    (fun j => eLpNorm (cutoffTraceDefect M m (m-((r+j:ℕ):ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure)
    (fun j => nativeSourceGenericWeakFrameProfile M.gamma (theta M) (9+r+j))
    (fun j hj => native_source_generic_weak_frame_profile_nonneg M.gamma (theta M) (9+r+j)
      hg0 ht0 hg (by omega))
    (fun j hj => by simpa only [Nat.add_assoc] using
      native_source_depth_generic_eLpNorm M h hM hg m hpast (r+j) (by omega))
    (fun j _ => by simpa only [Nat.add_assoc] using
      native_source_depth_exponential_eLpNorm M h hM hg m hpast (r+j))
  exact he.trans (ENNReal.ofReal_le_ofReal
    (native_source_generic_complete_weak_row_covers_exponential_tail M.gamma (theta M) r 1285
      hg0 hg ht0 hr (by norm_num)))

end
end ASDExplicitGamma.Native
