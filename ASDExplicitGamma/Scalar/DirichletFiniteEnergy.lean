module

public import ASDExplicitGamma.Scalar.DirichletPolynomial

/-! The exact finite-dimensional spectral energy identity for Dirichlet data. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Triadic Torus MeasureTheory

/-- The spectral Laplacian of the finite Dirichlet sine polynomial. -/
noncomputable def dirichletPolynomialLaplacian {d : ℕ} (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (beta : (Fin d → ℕ) → ℝ) (x : Vec d) : ℝ :=
  ∑ q ∈ S,(-beta q*cubeEig Q (natVec q))*cubeDirichletMode Q q x

/-- Parseval evaluates the actual finite sine-polynomial Laplacian energy. -/
theorem dirichlet_polynomial_laplacian_energy {d : ℕ} (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (beta : (Fin d → ℕ) → ℝ)
    (hS : ∀ q ∈ S,∀ i,q i≠0) :
    energy Q (dirichletPolynomialLaplacian Q S beta)=
      ∑ q ∈ S,beta q^2*cubeEig Q (natVec q)^2/modeMult q := by
  rw [energy_eq_integral_sq,← boxMeasure_eq_normalizedCubeMeasure]
  unfold dirichletPolynomialLaplacian cubeDirichletMode
  rw [integral_sq_sum_boxMode _ (cubeScaleFactor_pos' Q)]
  apply Finset.sum_congr rfl
  intro q hq
  rw [boxNormSq_eq_inv_modeMult _ q (fun i hi => hS q hq i)]
  ring

/-- The exact Hessian/Laplacian energy identity at every finite sine cutoff. -/
theorem dirichlet_finite_hessian_energy_identity {d : ℕ} (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (beta : (Fin d → ℕ) → ℝ)
    (hS : ∀ q ∈ S,∀ i,q i≠0) :
    (∑ j,∑ i,energy Q (dirichletTestHess Q S beta j i))=
      energy Q (dirichletPolynomialLaplacian Q S beta) := by
  rw [sum_sum_energy_dirichletTestHess Q S beta hS,
    dirichlet_polynomial_laplacian_energy Q S beta hS]

end ASDExplicitGamma.Scalar
