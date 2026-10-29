module

public import ASDExplicitGamma.Native.SourceRowsInterface
public import ASDExplicitGamma.Native.SmallerGammaWeak

/-! The exact row consumer of the smaller-γ source conclusion. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal
noncomputable section

/-- Convert the predecessor's six outward smaller-γ rows to the exact
certificate rationals. The actual-law quantities stay in
ENNReal throughout; only the closed rational cap comparison is cast to ℝ. -/
theorem native_source_rows_from_smaller_gamma
    (M : ABKModel 2) (m : ℤ)
    (hsource : NativeSourceSmallerGammaBounds M m) :
    NativeSourceRowsBounds M m := by
  have htheta : 0 ≤ theta M :=
    div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  constructor
  · intro r
    have hc := (native_source_exact_caps_of_certificate r).1
    have hcR : ((nativeCompletedMeanRows.getD r.val 0 : ℚ) : ℝ) ≤
        ((nativeSourceExactMeanCaps.getD r.val 0 : ℚ) : ℝ) := by
      exact_mod_cast hc
    exact (hsource.mean r).trans
      (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hcR htheta))
  · intro r
    have hc := (native_source_exact_caps_of_certificate r).2
    have hcR : ((nativeCompletedWeakRows.getD r.val 0 : ℚ) : ℝ) ≤
        ((nativeSourceExactWeakCaps.getD r.val 0 : ℚ) : ℝ) := by
      exact_mod_cast hc
    exact (hsource.weak r).trans
      (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hcR htheta))

end
end ASDExplicitGamma.Native
