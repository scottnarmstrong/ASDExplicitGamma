module

public import ASDExplicitGamma.Inverse.ClippedMatrixQuadraticNorm
public import ASDExplicitGamma.Inverse.StoppedPlanarFluxAlgebra

/-! Exact Euclidean loading bounds for the common planar flux transform. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
noncomputable section

/-- Euclidean operator control with the same coordinate dot product as the
response quadratic forms. There is no coordinate-supremum norm loss. -/
theorem matrix_loading_square_le (A : Mat 2) (v : Vec 2) :
    dotProduct (matVecMul A v) (matVecMul A v) ≤
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A‖^2*dotProduct v v := by
  let T := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A
  let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 v
  have he : T x=WithLp.toLp 2 (matVecMul A v) := by
    apply WithLp.ofLp_injective
    simp only [T,x,Matrix.ofLp_toEuclideanCLM]
    rfl
  have hh := pow_le_pow_left₀ (norm_nonneg (T x)) (T.le_opNorm x) 2
  rw [he,mul_pow,clipped_euclidean_norm_sq,clipped_euclidean_norm_sq] at hh
  exact hh

/-- The source planar transform preserves the exact operator norm. -/
theorem planar_flux_loading_square_le (A : Mat 2) (v : Vec 2) :
    dotProduct (matVecMul (planarFluxMatrix A) v) (matVecMul (planarFluxMatrix A) v) ≤
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A‖^2*dotProduct v v := by
  simpa only [planar_flux_matrix_norm] using matrix_loading_square_le (planarFluxMatrix A) v

end
end ASDExplicitGamma.Inverse
