module

public import ASDExplicitGamma.Scalar.DirichletLimit

/-! Exact square Dirichlet Hessian/Laplacian identity for every H2/H10 function. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Triadic Torus MeasureTheory Filter

/-- The energy of an L2 representative is the actual quotient norm squared. -/
theorem dirichlet_energy_eq_L2_norm_sq (Q : TriadicCube 2) (g : DirichletL2 Q)
    (f : Vec 2 → ℝ) (h : (g : Vec 2 → ℝ) =ᵐ[normalizedCubeMeasure Q] f) :
    energy Q f=‖g‖^2 := by
  rw [energy_eq_cubeLpNorm_sq Q ((memLp_congr_ae h).mp (Lp.memLp g)),Lp.norm_def]
  unfold cubeLpNorm
  rw [eLpNorm_congr_ae h]

/-- The exact square Dirichlet identity. Only the source H2 and zero-trace assumptions occur. -/
theorem dirichlet_square_hessian_identity (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) (H : HasWeakHessianOn (openCubeSet Q) u.toH1Function) :
    H.frobeniusNormalizedL2 Q=cubeLpNorm Q 2 (dirichletWeakLaplacian H) := by
  let f : DirichletL2 Q := (memLp_dirichlet_weak_laplacian H).toLp (dirichletWeakLaplacian H)
  obtain ⟨S,β,g,hS,hg,hlim⟩ := exists_dirichlet_polynomial_L2_approximation Q f
  let b (n : ℕ) (q : Fin 2 → ℕ) := -β n q/cubeEig Q (natVec q)
  let v (n : ℕ) := dirichletPolynomialH10 Q (S n) (b n)
  let K (n : ℕ) := dirichletPolynomialHessian Q (S n) (b n)
  have hK (n : ℕ) : dirichletWeakLaplacian (K n)=dirichletPolynomial Q (S n) (β n) := by
    funext x
    rw [dirichlet_polynomial_hessian_trace]
    exact congrFun (dirichlet_inverse_polynomial_laplacian Q (S n) (β n) (hS n)) x
  have hcoord (i j : Fin 2) := dirichlet_hessian_coordinates_tendsto Q u H v K g
    (fun n => by rw [hK];exact hg n) hlim i j
  have hl : Tendsto (fun n => (cubeVolume Q)⁻¹*(∑ i,∑ j,‖(K n).hessCoordToScalarL2 i j‖^2))
      atTop (nhds ((cubeVolume Q)⁻¹*(∑ i,∑ j,‖H.hessCoordToScalarL2 i j‖^2))) := by
    apply Tendsto.const_mul
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (hcoord i j).norm.pow 2
  have he (n : ℕ) : (cubeVolume Q)⁻¹*(∑ i,∑ j,‖(K n).hessCoordToScalarL2 i j‖^2)=‖g n‖^2 := by
    rw [dirichlet_polynomial_hessian_energy_coordinates Q (S n) (b n) (hS n)]
    rw [dirichlet_inverse_polynomial_laplacian Q (S n) (β n) (hS n)]
    exact dirichlet_energy_eq_L2_norm_sq Q (g n) _ (hg n)
  simp_rw [he] at hl
  have hsq := tendsto_nhds_unique hl (hlim.norm.pow 2)
  rw [← H.frobeniusNormalizedL2_sq Q] at hsq
  have hnf : ‖f‖=cubeLpNorm Q 2 (dirichletWeakLaplacian H) := Lp.norm_toLp _ _
  rw [hnf] at hsq
  have hn : 0 ≤ H.frobeniusNormalizedL2 Q := by
    unfold HasWeakHessianOn.frobeniusNormalizedL2
    exact mul_nonneg (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _) (Real.sqrt_nonneg _)
  exact (sq_eq_sq₀ hn (cubeLpNorm_nonneg Q 2 _)).mp hsq

end ASDExplicitGamma.Scalar
