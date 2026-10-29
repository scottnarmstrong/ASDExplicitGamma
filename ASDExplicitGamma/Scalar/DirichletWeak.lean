module

public import ASDExplicitGamma.Scalar.DirichletDensity
public import Homogenization.Sobolev.Foundations.CubeDirichletH2.Regularity
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.WeakDerivativeTestClosure

/-! Weak integration by parts for the actual zero-trace Dirichlet problem. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Triadic MeasureTheory
open scoped ENNReal

/-- A weak derivative can be tested against every actual zero-trace H1 function. -/
theorem weak_partial_test_H10 {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {u g : Vec d → ℝ} {i : Fin d} (hw : HasWeakPartialDerivOn U i u g)
    (hu : MemScalarL2 U u) (hg : MemScalarL2 U g) (φ : H10Function U) :
    (∫ x in U,u x*φ.toH1Function.grad x i ∂volume)=
      -∫ x in U,g x*φ x ∂volume := by
  apply hw.integral_mul_deriv_eq_neg_integral_mul_of_eLpNorm_approx hu hg
    φ.toH1Function.memL2 (φ.toH1Function.gradMemL2 i) φ.approx
    φ.approx_smooth φ.approx_hasCompactSupport φ.approx_support_subset
  · intro n
    exact (H10Function.ofContDiff hU (φ.approx_smooth n)
      (φ.approx_hasCompactSupport n) (φ.approx_support_subset n)).toH1Function.memL2
  · intro n
    exact (H10Function.ofContDiff hU (φ.approx_smooth n)
      (φ.approx_hasCompactSupport n) (φ.approx_support_subset n)).toH1Function.gradMemL2 i
  · exact φ.tendsto_approx
  · exact φ.tendsto_approx_grad i

/-- The actual weak Hessian trace is the distributional Laplacian. -/
noncomputable def dirichletWeakLaplacian {d : ℕ} {Q : TriadicCube d}
    {u : H10Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) u.toH1Function)
    (x : Vec d) : ℝ := ∑ i,H.hess i i x

/-- The weak Laplacian belongs to normalized L2. -/
theorem memLp_dirichlet_weak_laplacian {d : ℕ} {Q : TriadicCube d}
    {u : H10Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) u.toH1Function) :
    MemLp (dirichletWeakLaplacian H) 2 (normalizedCubeMeasure Q) := by
  apply memLp_normalized_of_memL2On
  exact memLp_finsetSum _ (fun i _ => H.hess_memL2 i i)

/-- The Poisson equation with forcing minus the true weak Laplacian needs no extra premise. -/
theorem dirichlet_weak_poisson_of_hessian {d : ℕ} (Q : TriadicCube d)
    (u : H10Function (openCubeSet Q)) (H : HasWeakHessianOn (openCubeSet Q) u.toH1Function) :
    CubeDirichletWeakPoissonProblem Q u (fun x => -dirichletWeakLaplacian H x) := by
  intro φ
  have hg (i : Fin d) := weak_partial_test_H10 (isOpen_openCubeSet Q) (H.weak_second i i)
    (u.toH1Function.gradMemL2 i) (H.hess_memL2 i i) φ
  have hi (i : Fin d) : Integrable (fun x => H.hess i i x*φ x)
      (volume.restrict (openCubeSet Q)) :=
    (H.hess_memL2 i i).integrable_mul φ.toH1Function.memL2
  have hgi (i : Fin d) : Integrable (fun x => u.toH1Function.grad x i*φ.toH1Function.grad x i)
      (volume.restrict (openCubeSet Q)) :=
    (u.toH1Function.gradMemL2 i).integrable_mul (φ.toH1Function.gradMemL2 i)
  simp only [vecDot]
  rw [integral_finsetSum _ (fun i _ => hgi i)]
  simp_rw [hg]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hi i), ← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp [dirichletWeakLaplacian,Finset.sum_mul]

end ASDExplicitGamma.Scalar
