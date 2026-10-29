module

public import ASDExplicitGamma.Native.SourceSmallerGammaInterface
public import ASDExplicitGamma.Native.SourceRowsExactCaps

/-! Stable actual-law NA-SOURCE-ROWS interface, with the exact completed
ordinary-mean coordinate at offset zero and the six exact certificate caps. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal
noncomputable section

/-- The six actual completed means and carried weak charges in the true
completed frame. These are conclusions, not assumed source tables. -/
structure NativeSourceRowsBounds (M : ABKModel 2) (m : ℤ) : Prop where
  mean_exact : ∀ r : Fin 6, nativeCompletedSourceMean M m r.val ≤
    ENNReal.ofReal (theta M*((nativeSourceExactMeanCaps.getD r.val 0:ℚ):ℝ))
  weak_exact : ∀ r : Fin 6, nativeCompletedSourceWeak M m r.val ≤
    ENNReal.ofReal (theta M*((nativeSourceExactWeakCaps.getD r.val 0:ℚ):ℝ))

/-- The exact smaller-gamma producer implies all six exact consumer rows.
The sole producer premise is explicit; it will be discharged by the source
chain once its boundary and refined inputs are assembled. -/
theorem native_source_rows_of_smaller_gamma (M : ABKModel 2) (m : ℤ)
    (hsource : NativeSourceSmallerGammaBounds M m) : NativeSourceRowsBounds M m := by
  have ht0 : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  constructor
  · intro r
    have hc := (native_source_exact_caps_of_certificate r).1
    have hcR : ((nativeCompletedMeanRows.getD r.val 0:ℚ):ℝ) ≤
        ((nativeSourceExactMeanCaps.getD r.val 0:ℚ):ℝ) := by exact_mod_cast hc
    exact (hsource.mean r).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcR ht0))
  · intro r
    have hc := (native_source_exact_caps_of_certificate r).2
    have hcR : ((nativeCompletedWeakRows.getD r.val 0:ℚ):ℝ) ≤
        ((nativeSourceExactWeakCaps.getD r.val 0:ℚ):ℝ) := by exact_mod_cast hc
    exact (hsource.weak r).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcR ht0))

/-- Legacy six-digit mean display, derived from the exact row conclusion. -/
theorem NativeSourceRowsBounds.mean {M : ABKModel 2} {m : ℤ}
    (hrows : NativeSourceRowsBounds M m) (r : Fin 6) :
    nativeCompletedSourceMean M m r.val≤
      ENNReal.ofReal (theta M*((nativeCompletedMeanCaps.getD r.val 0 : ℚ) : ℝ)) := by
  have ht0 : 0≤theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hc : ((nativeSourceExactMeanCaps.getD r.val 0 : ℚ) : ℝ)≤
      ((nativeCompletedMeanCaps.getD r.val 0 : ℚ) : ℝ) := by
    exact_mod_cast (native_source_exact_caps_le_rounded r).1
  exact (hrows.mean_exact r).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hc ht0))

/-- Legacy six-digit weak display, derived from the exact row conclusion. -/
theorem NativeSourceRowsBounds.weak {M : ABKModel 2} {m : ℤ}
    (hrows : NativeSourceRowsBounds M m) (r : Fin 6) :
    nativeCompletedSourceWeak M m r.val≤
      ENNReal.ofReal (theta M*((nativeCompletedWeakCaps.getD r.val 0 : ℚ) : ℝ)) := by
  have ht0 : 0≤theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hc : ((nativeSourceExactWeakCaps.getD r.val 0 : ℚ) : ℝ)≤
      ((nativeCompletedWeakCaps.getD r.val 0 : ℚ) : ℝ) := by
    exact_mod_cast (native_source_exact_caps_le_rounded r).2
  exact (hrows.weak_exact r).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hc ht0))

/-- Exact depth-four mean cap retained by the lower and main interfaces. -/
theorem NativeSourceRowsBounds.mean_four {M : ABKModel 2} {m : ℤ}
    (hrows : NativeSourceRowsBounds M m) :
    nativeCompletedSourceMean M m 4≤ENNReal.ofReal
      (theta M*(8392611373095084661337932723209/10^32 : ℝ)) := by
  have hh := hrows.mean_exact (4 : Fin 6)
  norm_num [nativeSourceExactMeanCaps] at hh ⊢
  exact hh

/-- Exact depth-five initial mean required by MA-ENVELOPE-A. -/
theorem NativeSourceRowsBounds.mean_five {M : ABKModel 2} {m : ℤ}
    (hrows : NativeSourceRowsBounds M m) :
    nativeCompletedSourceMean M m 5≤ENNReal.ofReal
      (theta M*(4441091003104432097305984305313/(5*10^31) : ℝ)) := by
  have hh := hrows.mean_exact (5 : Fin 6)
  norm_num [nativeSourceExactMeanCaps] at hh ⊢
  exact hh

end
end ASDExplicitGamma.Native
