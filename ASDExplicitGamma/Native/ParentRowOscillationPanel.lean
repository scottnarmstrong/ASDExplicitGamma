module

public import ASDExplicitGamma.Native.ParentRowOscillationSums
public import ASDExplicitGamma.Native.ParentRowOscillationFields

/-! Actual complete-band oscillations paid by their selected panel fields. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Triadic Cold Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- The summed physical oscillation energy fits the exact stored sign-specific
panel field, retaining its full theta factor. -/
theorem parent_row_band_oscillation_panel
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) (plus : Bool) :
    let Q := originCube 2 n
    (∑ i : Fin (j.val+1),descendantsAverage Q 5 (fun U =>
      oldSignedFlatOscillationSize Q U
        (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
        (q3ModelLength (n+((i.val+1:ℕ):ℤ))) plus^2))≤
      theta M*((parentRowFields j).getD (if plus then 4 else 5) 0)^2 := by
  intro Q
  have hh := parent_row_band_oscillation_energy M h hg n hstate j plus
  dsimp only at hh
  have ha := nativeList_getD_nonneg (parentRowFields j) (parent_row_fields_valid j).2 1
  rw [parent_row_oscillation_field,parentRowOscillationValue,←parent_row_a2_eq]
  rw [mul_pow,Real.sq_sqrt (mul_nonneg ha (by norm_num : (0:ℝ)≤156/5))]
  exact hh.trans_eq (by ring)

/-- The shell Euclidean oscillation norm is controlled without a shell-count
loss; the selected nonnegative panel coefficient receives sqrt(theta). -/
theorem parent_row_band_oscillation_root
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) (plus : Bool) :
    let Q := originCube 2 n
    Real.sqrt (∑ i : Fin (j.val+1),descendantsAverage Q 5 (fun U =>
      oldSignedFlatOscillationSize Q U
        (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
        (q3ModelLength (n+((i.val+1:ℕ):ℤ))) plus^2))≤
      Real.sqrt (theta M)*(parentRowFields j).getD (if plus then 4 else 5) 0 := by
  intro Q
  have hh := Real.sqrt_le_sqrt (parent_row_band_oscillation_panel M h hg n hstate j plus)
  rw [Real.sqrt_mul (cold_theta_pos M).le,Real.sqrt_sq
    (nativeList_getD_nonneg (parentRowFields j) (parent_row_fields_valid j).2 _)] at hh
  exact hh

end
end ASDExplicitGamma.Native
