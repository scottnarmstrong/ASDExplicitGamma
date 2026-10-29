module

public import ASDExplicitGamma.Scalar.UpperCellEnergyDerivativeSeries

/-! Actual finite-band derivative covariance at the depth-fourteen cell. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Algsuperdiff.Section3 Finset
noncomputable section

/-- Exact cancellation of the absolute shell scale against the physical cell.
The derivative order is retained in the source-depth decay. -/
theorem upper_cell_derivative_scale_identity (n gamma k : ℝ) (j : ℕ) :
    (3:ℝ)^(2*k*(n-14))*((3:ℝ)^(2*gamma*(j:ℝ))*(3:ℝ)^(-2*k*(n+(j:ℝ)))) =
      (3:ℝ)^(-28*k)*((3:ℝ)^(2*gamma-2*k))^j := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
  rw [← Real.rpow_add (by norm_num : (0:ℝ)<3),
    ← Real.rpow_add (by norm_num : (0:ℝ)<3),
    ← Real.rpow_add (by norm_num : (0:ℝ)<3)]
  congr 1
  ring

/-- The actual normalized covariance sum at each positive derivative order
is at most gamma times the square of the depth-fourteen derivative scale.
All shells are summed before taking the square root. -/
theorem upper_cell_band_derivative_variance_le
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (hg : M.gamma ≤ gammaZero)
    (hstate : nativeInductionState M h n) (k height : ℕ) (hk : 1 ≤ k) :
    (3:ℝ)^(2*(k:ℝ)*((n:ℝ)-14))*
      (∑ j ∈ Ico 1 (height+1),
        (h^2*(3:ℝ)^(2*M.gamma*((n+(j:ℤ):ℤ):ℝ))/(Annealed.sigmaBar M n:ℝ)^2)*
          (3:ℝ)^(-2*(k:ℝ)*((n+(j:ℤ):ℤ):ℝ))) ≤
      M.gamma*(3:ℝ)^(-28*(k:ℝ)) := by
  let R := (3:ℝ)^(2*(k:ℝ)*((n:ℝ)-14))
  let q := (3:ℝ)^(2*M.gamma-2*(k:ℝ))
  have hterm (j : ℕ) :
      R*((h^2*(3:ℝ)^(2*M.gamma*((n+(j:ℤ):ℤ):ℝ))/(Annealed.sigmaBar M n:ℝ)^2)*
          (3:ℝ)^(-2*(k:ℝ)*((n+(j:ℤ):ℤ):ℝ))) ≤
      (3:ℝ)^(-28*(k:ℝ))*((9/2:ℝ)*M.gamma*q^j) := by
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (upper_cell_fresh_shell_variance_le M h n j hstate)
        (Real.rpow_nonneg (by norm_num : (0:ℝ)≤3) (-2*(k:ℝ)*((n+(j:ℤ):ℤ):ℝ))))
      (show 0 ≤ R by dsimp only [R]; positivity)
    refine hh.trans_eq ?_
    dsimp only [R,q]
    push_cast
    calc
      _ = ((9/2:ℝ)*M.gamma)*((3:ℝ)^(2*(k:ℝ)*((n:ℝ)-14))*
          ((3:ℝ)^(2*M.gamma*(j:ℝ))*(3:ℝ)^(-2*(k:ℝ)*((n:ℝ)+(j:ℝ))))) := by ring
      _ = _ := by rw [upper_cell_derivative_scale_identity]; ring
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Ico 1 (height+1)) => hterm j)
  rw [← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum] at hsum
  have hgsmall : M.gamma ≤ (1/6:ℝ) := hg.trans (by norm_num [gammaZero])
  have hgeom := upper_cell_derivative_geometric_sum M.gamma M.shellPrefix.gamma_pos.le
    hgsmall k height hk
  have hlast := mul_le_mul_of_nonneg_left hgeom
    (Real.rpow_nonneg (by norm_num : (0:ℝ)≤3) (-28*(k:ℝ)))
  exact hsum.trans (hlast.trans_eq (by ring))

end
end ASDExplicitGamma.Scalar
