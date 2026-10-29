module

public import ASDExplicitGamma.Native.CompletedPrefixEndpoint
public import Mathlib.Basic.ENNReal.Real

/-! Positive completed-prefix endpoint comparison and its outward displays.
The residual is kept before comparing any finite-prefix summand. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.Native
noncomputable section

/-- The exact endpoint rows imply the six outward mean and weak displays. -/
theorem native_completed_prefix_display_caps
    (theta : ℝ) (htheta : 0 ≤ theta) (r : Fin 6) :
    ENNReal.ofReal (theta*((nativeCompletedMeanRows.getD r.val 0 : ℚ) : ℝ)) ≤
      ENNReal.ofReal (theta*((nativeCompletedMeanCaps.getD r.val 0 : ℚ) : ℝ)) ∧
    ENNReal.ofReal (theta*((nativeCompletedWeakRows.getD r.val 0 : ℚ) : ℝ)) ≤
      ENNReal.ofReal (theta*((nativeCompletedWeakCaps.getD r.val 0 : ℚ) : ℝ)) := by
  have hh := native_completed_source_caps r
  exact ⟨ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    ((Rat.cast_le (K := ℝ)).mpr hh.1) htheta),
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      ((Rat.cast_le (K := ℝ)).mpr hh.2.le) htheta)⟩

end
end ASDExplicitGamma.Native
