module

public import ASDExplicitGamma.Native.ParentRowBoundaryFields

/-! Separate actual parent boundary charges paid by their exact panel fields. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Algsuperdiff.Section3
noncomputable section

/-- Each actual complete centered boundary sum fits its own certified
coefficient, preserving theta and the original sign. -/
theorem parent_row_band_beta_panel
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) (plus : Bool) :
    (∑ i : Fin (j.val+1),parentRowBeta n 5
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ))) plus)≤
      theta M*(parentRowFields j).getD (if plus then 6 else 7) 0 := by
  rw [parent_row_boundary_field]
  exact parent_row_band_beta_value M h hg n hstate (j.val+1) plus

end
end ASDExplicitGamma.Native
