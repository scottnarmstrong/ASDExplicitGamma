module

public import ASDExplicitGamma.Inverse.StoppedMidpointGradient
public import ASDExplicitGamma.Response.FrameAlgebra

/-! Source linear planar flux transform, with its exact Euclidean operator
norm. This is the geometry transform, not the stochastic
pure-flux generator. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization ASDExplicitGamma.Response
noncomputable section

def planarFluxMatrix (F : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  responsePlanarJ*F*star responsePlanarJ

theorem planar_quarter_turn_unitary : responsePlanarJ ∈ unitary (Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Unitary.mem_iff]
  constructor <;> ext i k <;> fin_cases i <;> fin_cases k <;>
    norm_num [responsePlanarJ,Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply]

/-- Literal source L(F)=(tr F)I-F^T in dimension two. -/
theorem planar_flux_matrix_source (F : Matrix (Fin 2) (Fin 2) ℝ) :
    planarFluxMatrix F=Matrix.trace F • (1 : Matrix (Fin 2) (Fin 2) ℝ)-F.transpose := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [planarFluxMatrix,responsePlanarJ,Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply,Matrix.trace,Matrix.vecMul,dotProduct]

/-- Orthogonal conjugation preserves the exact Euclidean operator norm. -/
theorem planar_flux_matrix_norm (F : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (planarFluxMatrix F)‖=
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) F‖ := by
  have hJ := Unitary.map_mem (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)) planar_quarter_turn_unitary
  rw [planarFluxMatrix,map_mul,map_mul,map_star]
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem_iff.mpr hJ),CStarRing.norm_mem_unitary_mul _ hJ]

theorem planar_flux_matrix_one : planarFluxMatrix 1=1 := by
  rw [planarFluxMatrix,mul_one,Unitary.mul_star_self_of_mem planar_quarter_turn_unitary]

theorem planar_flux_matrix_zero : planarFluxMatrix 0=0 := by
  rw [planarFluxMatrix,mul_zero,zero_mul]

/-- The explicit coordinate form fixes the source column-divergence signs. -/
theorem planar_flux_matrix_apply (F : Matrix (Fin 2) (Fin 2) ℝ) (q : Vec 2) :
    matVecMul (planarFluxMatrix F) q=
      ![F 1 1*q 0-F 1 0*q 1,-F 0 1*q 0+F 0 0*q 1] := by
  rw [planar_flux_matrix_source]
  funext i
  fin_cases i <;> simp [matVecMul,Fin.sum_univ_two,Matrix.trace]
  ring

end
end ASDExplicitGamma.Inverse
