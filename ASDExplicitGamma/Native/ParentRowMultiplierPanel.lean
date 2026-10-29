module

public import ASDExplicitGamma.Native.ParentRowSourceMultiplier
public import ASDExplicitGamma.Native.ParentRowMultiplierFields

/-! Actual complete-band multipliers paid by the exact selected panel fields. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Main Triadic Cold Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- The complete parent source coefficient receives exactly sqrt(theta)
times the certified source field, without a shell-count loss. -/
theorem parent_row_band_source_panel
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) :
    Real.sqrt (∑ i : Fin (j.val+1),(parentBoundaryPotentialSourceClock (originCube 2 n) 5
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ))))^2)≤
      Real.sqrt (theta M)*(parentRowFields j).getD 2 0 := by
  have he := parent_row_multiplier_field j false
  simp only [Bool.false_eq_true,ite_false] at he
  rw [he,parentRowMultiplierValue]
  simpa only [Bool.false_eq_true,ite_false,mul_comm,mul_left_comm,mul_assoc] using
    parent_row_band_source_multiplier M h hg n hstate (j.val+1)

/-- The sharp complete derivative coefficient keeps its sqrt(2) gain
while using the very same stored derivative field. -/
theorem parent_row_band_derivative_panel
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) :
    Real.sqrt (∑ i : Fin (j.val+1),(Real.sqrt 2*oldSignedDerivativeKappa
      (cubeScaleFactor (originCube 2 n)/3^5)
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ))).val)^2)≤
      Real.sqrt (theta M)*(parentRowFields j).getD 3 0 := by
  have he := parent_row_multiplier_field j true
  simp only [ite_true] at he
  rw [he,parentRowMultiplierValue]
  simpa only [ite_true,mul_comm,mul_left_comm,mul_assoc] using
    parent_row_band_derivative_multiplier M h hg n hstate (j.val+1)

end
end ASDExplicitGamma.Native
