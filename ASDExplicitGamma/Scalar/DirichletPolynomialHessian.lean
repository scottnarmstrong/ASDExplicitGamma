module

public import ASDExplicitGamma.Scalar.DirichletDifferentiation
public import ASDExplicitGamma.Scalar.DirichletWeak

/-! The actual weak Hessian of each finite Dirichlet sine polynomial. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Triadic Torus MeasureTheory

/-- The spectral finite Hessian is the actual weak Hessian of the H10 realization. -/
noncomputable def dirichletPolynomialHessian {d : ℕ} (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (β : (Fin d → ℕ) → ℝ) :
    HasWeakHessianOn (openCubeSet Q) (dirichletPolynomialH10 Q S β).toH1Function where
  hess := dirichletTestHess Q S β
  hess_memL2 i j := by
    simpa only [dirichletTestFieldH1_grad] using (dirichletTestFieldH1 Q S β i).gradMemL2 j
  weak_second i j := by
    intro φ hφ hc hs
    have h := (dirichletTestFieldH1 Q S β i).hasWeakGradient j φ hφ hc hs
    simp only [dirichletTestFieldH1_toFun,dirichletTestFieldH1_grad] at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards [dirichlet_polynomial_H10_gradient Q S β] with x hx
    rw [hx]

/-- The trace of the actual finite Hessian is precisely its spectral Laplacian. -/
theorem dirichlet_polynomial_hessian_trace {d : ℕ} (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (β : (Fin d → ℕ) → ℝ) (x : Vec d) :
    dirichletWeakLaplacian (dirichletPolynomialHessian Q S β) x=
      dirichletPolynomialLaplacian Q S β x := by
  unfold dirichletWeakLaplacian dirichletPolynomialHessian dirichletTestHess
  rw [Finset.sum_comm]
  unfold dirichletPolynomialLaplacian
  apply Finset.sum_congr rfl
  intro q _
  simp only [dirichletHessCoef,dirichletHessSet,ite_true]
  unfold cubeDirichletMode cubeEig
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end ASDExplicitGamma.Scalar
