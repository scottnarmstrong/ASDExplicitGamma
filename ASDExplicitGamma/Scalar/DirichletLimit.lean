module

public import ASDExplicitGamma.Scalar.DirichletStability
public import ASDExplicitGamma.Scalar.DirichletInversePolynomial

/-! Stability passage from finite sine polynomials to a genuine weak Hessian. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Triadic MeasureTheory Filter

/-- Converging Laplacians force every actual Dirichlet Hessian coordinate to converge in L2. -/
theorem dirichlet_hessian_coordinates_tendsto (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) (H : HasWeakHessianOn (openCubeSet Q) u.toH1Function)
    (v : ℕ → H10Function (openCubeSet Q))
    (K : ∀ n,HasWeakHessianOn (openCubeSet Q) (v n).toH1Function)
    (g : ℕ → DirichletL2 Q)
    (hg : ∀ n,(g n : Vec 2 → ℝ) =ᵐ[normalizedCubeMeasure Q] dirichletWeakLaplacian (K n))
    (hlim : Tendsto g atTop (nhds ((memLp_dirichlet_weak_laplacian H).toLp (dirichletWeakLaplacian H))))
    (i j : Fin 2) :
    Tendsto (fun n => (K n).hessCoordToScalarL2 i j) atTop (nhds (H.hessCoordToScalarL2 i j)) := by
  let f : DirichletL2 Q := (memLp_dirichlet_weak_laplacian H).toLp (dirichletWeakLaplacian H)
  change Tendsto g atTop (nhds f) at hlim
  have hforce (n : ℕ) :
      cubeLpNorm Q 2 (fun x => -dirichletWeakLaplacian (dirichletHessianSub H (K n)) x)=‖g n-f‖ := by
    rw [Lp.norm_def]
    unfold cubeLpNorm
    apply congrArg ENNReal.toReal
    apply eLpNorm_congr_ae
    filter_upwards [hg n,(memLp_dirichlet_weak_laplacian H).coeFn_toLp,Lp.coeFn_sub (g n) f]
      with x hx hf hs
    rw [hs]
    change (g n : Vec 2 → ℝ) x=dirichletWeakLaplacian (K n) x at hx
    change (f : Vec 2 → ℝ) x=dirichletWeakLaplacian H x at hf
    simp only [Pi.sub_apply,hx,hf,dirichletWeakLaplacian,dirichletHessianSub,Finset.sum_sub_distrib]
    ring
  have hb (n : ℕ) := dirichlet_hessian_coordinate_bound Q (u-v n) (dirichletHessianSub H (K n)) i j
  simp only [dirichlet_hessian_sub_L2,hforce] at hb
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hn : Tendsto (fun n => ‖g n-f‖) atTop (nhds 0) := by
    simpa only [sub_self,norm_zero] using (hlim.sub_const f).norm
  have hc := hn.const_mul (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityConstantExact Q)
  simp only [mul_zero] at hc
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hc
  rw [norm_sub_rev]
  exact hb n

end ASDExplicitGamma.Scalar
