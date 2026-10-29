module

public import ASDExplicitGamma.Inverse.StoppedMeshHatBounds
public import ASDExplicitGamma.Triadic.DiagInterpolant
public import ASDExplicitGamma.Triadic.PlanarDirectionLinear
public import ASDExplicitGamma.Inverse.CompatibleMidpoint
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-! The sharp coordinate-column and Euclidean operator payments for one
source midpoint mesh group. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization ASDExplicitGamma.Triadic
noncomputable section

private theorem planar_cauchy (a b u v : ℝ) :
    (a*u+b*v)^2 ≤ (a^2+b^2)*(u^2+v^2) := by
  nlinarith only [sq_nonneg (a*v-b*u)]

/-- A two-by-two matrix whose four entries are bounded by q has Euclidean
operator norm at most 2q. The norm convention is explicit. -/
theorem planar_euclidean_operator_bound (A : Matrix (Fin 2) (Fin 2) ℝ)
    (q : ℝ) (hq : 0 ≤ q) (hA : ∀ i k, |A i k| ≤ q) :
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A‖ ≤ 2*q := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*q*‖x‖)).mp
  have hsq (i k : Fin 2) : (A i k)^2 ≤ q^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hq).mpr (hA i k)
  have hrow (i : Fin 2) : (A i 0*x 0+A i 1*x 1)^2 ≤ 2*q^2*((x 0)^2+(x 1)^2) := by
    apply (planar_cauchy (A i 0) (A i 1) (x 0) (x 1)).trans
    exact mul_le_mul_of_nonneg_right (by linarith only [hsq i 0,hsq i 1]) (by positivity)
  rw [mul_pow,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two,Fin.sum_univ_two]
  simp only [Matrix.ofLp_toEuclideanCLM,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  nlinarith only [hrow 0,hrow 1]

end
end ASDExplicitGamma.Inverse
