module

public import ASDExplicitGamma.Scalar.DirichletFiniteEnergy
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Transport

/-! Identification of the derivatives of finite square sine polynomials. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Triadic Torus MeasureTheory

/-- The actual line derivative of a sine polynomial is the spectral gradient. -/
theorem hasDerivAt_dirichletPolynomial {d : ℕ} (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (β : (Fin d → ℕ) → ℝ) (i : Fin d) (x : Vec d) :
    HasDerivAt (fun t => dirichletPolynomial Q S β (Function.update x i t))
      (dirichletTestField Q S β i x) (x i) := by
  have h := HasDerivAt.fun_sum (u := S) fun q _ =>
    (hasDerivAt_boxMode_update (cubeCorner Q) (cubeScaleFactor Q)
      Finset.univ (natVec q) i x).const_mul (β q)
  convert h using 1
  · rfl
  · simp only [Finset.mem_univ,ite_true]
    unfold dirichletTestField cubeDirichletMixedMode cubeFreq
    apply Finset.sum_congr rfl
    intro q _
    ring

/-- The full coordinate derivative of a sine polynomial is its explicit gradient. -/
theorem fderiv_dirichletPolynomial_apply {d : ℕ} (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (β : (Fin d → ℕ) → ℝ) (i : Fin d) (x : Vec d) :
    (fderiv ℝ (dirichletPolynomial Q S β) x) (basisVec i)=dirichletTestField Q S β i x := by
  have hf : DifferentiableAt ℝ (dirichletPolynomial Q S β) x :=
    ((dirichlet_polynomial_contDiff Q S β).differentiable (by simp)) x
  have hline : HasDerivAt (fun t => Function.update x i t) (basisVec i) (x i) := by
    convert (hasFDerivAt_update x (x i)).hasDerivAt using 1
    ext k
    by_cases hki : k=i <;> simp [basisVec,hki]
  have hf' : DifferentiableAt ℝ (dirichletPolynomial Q S β) (Function.update x i (x i)) := by
    simpa using hf
  have hchain := fderiv_comp_deriv (l := dirichletPolynomial Q S β)
    (f := fun t => Function.update x i t) (x := x i) hf' hline.differentiableAt
  rw [hline.deriv,Function.update_eq_self] at hchain
  change deriv (fun t => dirichletPolynomial Q S β (Function.update x i t)) (x i)=_ at hchain
  rw [(hasDerivAt_dirichletPolynomial Q S β i x).deriv] at hchain
  exact hchain.symm

/-- The H10 realization has the actual finite spectral gradient almost everywhere. -/
theorem dirichlet_polynomial_H10_gradient {d : ℕ} (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (β : (Fin d → ℕ) → ℝ) :
    (dirichletPolynomialH10 Q S β).toH1Function.grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x i => dirichletTestField Q S β i x := by
  let v := H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q) ((dirichlet_polynomial_contDiff Q S β).of_le (by simp))
  have hv := Book.Ch03.H1Function.grad_ae_eq_of_toFun_ae_eq (isOpen_openCubeSet Q)
    (u := (dirichletPolynomialH10 Q S β).toH1Function) (v := v)
    (dirichlet_polynomial_H10_value Q S β)
  filter_upwards [hv] with x hx
  ext i
  rw [hx]
  exact fderiv_dirichletPolynomial_apply Q S β i x

end ASDExplicitGamma.Scalar
