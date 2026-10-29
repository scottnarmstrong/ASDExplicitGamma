module

public import ASDExplicitGamma.Scalar.DirichletPolynomialHessian

/-! Stability of actual weak Dirichlet Hessian coordinates. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Triadic MeasureTheory

/-- A Hessian row is itself a genuine H1 function. -/
noncomputable def dirichletHessianRow {d : ℕ} {U : Set (Vec d)} {u : H1Function U}
    (H : HasWeakHessianOn U u) (i : Fin d) : H1Function U where
  toFun x := u.grad x i
  grad x j := H.hess i j x
  memL2 := u.gradMemL2 i
  gradMemL2 := H.hess_memL2 i
  hasWeakGradient := H.weak_second i

/-- Subtracting two zero-trace functions subtracts their true weak Hessians. -/
noncomputable def dirichletHessianSub {d : ℕ} {U : Set (Vec d)}
    {u v : H10Function U} (H : HasWeakHessianOn U u.toH1Function)
    (K : HasWeakHessianOn U v.toH1Function) :
    HasWeakHessianOn U (u-v).toH1Function where
  hess i j x := H.hess i j x-K.hess i j x
  hess_memL2 i j := (H.hess_memL2 i j).sub (K.hess_memL2 i j)
  weak_second i j := by
    have h := (dirichletHessianRow H i-dirichletHessianRow K i).hasWeakGradient j
    change HasWeakPartialDerivOn U j (fun x => (u.toH1Function-v.toH1Function).grad x i) _
    simpa only [H1Function.sub_toFun,H1Function.sub_grad,Pi.sub_apply,
      dirichletHessianRow] using h

/-- The Hessian subtraction agrees with subtraction in the actual L2 quotient. -/
theorem dirichlet_hessian_sub_L2 {d : ℕ} {U : Set (Vec d)}
    {u v : H10Function U} (H : HasWeakHessianOn U u.toH1Function)
    (K : HasWeakHessianOn U v.toH1Function) (i j : Fin d) :
    (dirichletHessianSub H K).hessCoordToScalarL2 i j=
      H.hessCoordToScalarL2 i j-K.hessCoordToScalarL2 i j := rfl

/-- The qualitative Dirichlet regularity theorem controls any supplied genuine Hessian. -/
theorem dirichlet_hessian_coordinate_bound (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) (H : HasWeakHessianOn (openCubeSet Q) u.toH1Function)
    (i j : Fin 2) :
    ‖H.hessCoordToScalarL2 i j‖ ≤
      CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityConstantExact Q *
        cubeLpNorm Q 2 (fun x => -dirichletWeakLaplacian H x) := by
  have hr := CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityExact Q
  obtain ⟨K,hK⟩ := hr.2 u _ (memLp_dirichlet_weak_laplacian H).neg
    (dirichlet_weak_poisson_of_hessian Q u H)
  have he : H.hessCoordToScalarL2 i j=K.hessCoordToScalarL2 i j := by
    apply Lp.ext
    have ha := HasWeakPartialDerivOn.ae_eq (isOpen_openCubeSet Q)
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((H.hess_memL2 i j).locallyIntegrable (by norm_num)))
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((K.hess_memL2 i j).locallyIntegrable (by norm_num)))
      (H.weak_second i j) (K.weak_second i j)
    exact ((H.hess_memL2 i j).coeFn_toLp).trans (ha.trans ((K.hess_memL2 i j).coeFn_toLp).symm)
  rw [he]
  apply le_trans _ hK
  unfold HasWeakHessianOn.hessianCoordL2NormSum
  exact (Finset.single_le_sum (fun k _ => norm_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => norm_nonneg _)
      (Finset.mem_univ i))

end ASDExplicitGamma.Scalar
