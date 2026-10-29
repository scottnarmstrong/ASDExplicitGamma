module

public import ASDExplicitGamma.Scalar.DirichletPolynomialHessian
public import ASDExplicitGamma.Scalar.DirichletApproximation
public import Homogenization.Sobolev.Foundations.WeakHessianEuclidean

/-! Exact finite Dirichlet inverse and its physical Hessian energy. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Triadic Torus MeasureTheory

/-- Inverting the nonzero sine eigenvalues gives the actual desired Laplacian. -/
theorem dirichlet_inverse_polynomial_laplacian (Q : TriadicCube 2)
    (S : Finset (Fin 2 → ℕ)) (β : (Fin 2 → ℕ) → ℝ)
    (hS : ∀ q ∈ S,∀ i,q i≠0) :
    dirichletPolynomialLaplacian Q S (fun q => -β q/cubeEig Q (natVec q))=
      dirichletPolynomial Q S β := by
  funext x
  apply Finset.sum_congr rfl
  intro q hq
  have he : cubeEig Q (natVec q)≠0 :=
    (cubeEig_natVec_pos Q (fun hz => hS q hq 0 (congrFun hz 0))).ne'
  dsimp
  field_simp

/-- The normalized energy of a genuine weak Hessian is its exact coordinate L2 sum. -/
theorem dirichlet_hessian_energy_coordinates (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) (H : HasWeakHessianOn (openCubeSet Q) u.toH1Function) :
    (∑ i,∑ j,energy Q (H.hess i j))=
      (cubeVolume Q)⁻¹*(∑ i,∑ j,‖H.hessCoordToScalarL2 i j‖^2) := by
  simp_rw [energy_eq_integral_sq,H.integral_hess_sq_normalizedCubeMeasure Q]
  simp only [Finset.mul_sum]

/-- The finite polynomial energy identity is an identity for the actual weak Hessian. -/
theorem dirichlet_polynomial_hessian_energy_coordinates (Q : TriadicCube 2)
    (S : Finset (Fin 2 → ℕ)) (β : (Fin 2 → ℕ) → ℝ)
    (hS : ∀ q ∈ S,∀ i,q i≠0) :
    (cubeVolume Q)⁻¹*(∑ i,∑ j,‖(dirichletPolynomialHessian Q S β).hessCoordToScalarL2 i j‖^2)=
      energy Q (dirichletPolynomialLaplacian Q S β) := by
  rw [← dirichlet_hessian_energy_coordinates]
  exact dirichlet_finite_hessian_energy_identity Q S β hS

end ASDExplicitGamma.Scalar
