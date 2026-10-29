module

public import ASDExplicitGamma.Native.ParentBoundaryPoincare
public import ASDExplicitGamma.Native.OldSignedNormalizedEnergy
public import ASDExplicitGamma.Scalar.DirichletWeak

/-! Sharp derivative-only clock for actual zero-boundary parent potentials. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
noncomputable section

/-- Genuine weak integration by parts identifies the parent gradient
energy with its signed Laplacian pairing. -/
theorem parent_boundary_gradient_laplacian_pairing (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u.toH1Function) :
    (∑ i : Fin 2,energy Q (fun x => u.toH1Function.grad x i)) =
      -pairing Q u.toH1Function.toFun (dirichletWeakLaplacian H) := by
  have hp := dirichlet_weak_poisson_of_hessian Q u H u
  rw [←old_signed_vector_energy_normalization Q u.toH1Function.grad_memVectorL2,
    ←real_inner_self_eq_norm_sq,inner_toHilbertVectorL2OfVecField_eq_integral,hp]
  rw [pairing,cubeAverage_eq_integral_normalizedCubeMeasure,integral_normalized_eq_open]
  have he : (∫ x in openCubeSet Q,(-dirichletWeakLaplacian H x)*u x) =
      -(∫ x in openCubeSet Q,u x*dirichletWeakLaplacian H x) := by
    rw [←integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by ring)
  rw [he]
  ring

/-- The sharp parent H10 gradient clock follows from actual weak
integration by parts and the first Dirichlet eigenvalue. -/
theorem parent_boundary_gradient_laplacian_clock (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u.toH1Function) :
    (∑ i : Fin 2,energy Q (fun x => u.toH1Function.grad x i)) ≤
      cubeScaleFactor Q^2/(2*Real.pi^2)*energy Q (dirichletWeakLaplacian H) := by
  let G := ∑ i : Fin 2,energy Q (fun x => u.toH1Function.grad x i)
  let C := cubeScaleFactor Q^2/(2*Real.pi^2)
  have hG : 0≤G := Finset.sum_nonneg (fun i _ => energy_nonneg Q _)
  have hE := energy_nonneg Q u.toH1Function.toFun
  have hL := energy_nonneg Q (dirichletWeakLaplacian H)
  have hp := abs_pairing_le Q u.toH1Function.memL2_normalizedCubeMeasure
    (memLp_dirichlet_weak_laplacian H)
  have he : |pairing Q u.toH1Function.toFun (dirichletWeakLaplacian H)|=G := by
    rw [←abs_neg,←parent_boundary_gradient_laplacian_pairing,abs_of_nonneg hG]
  rw [he] at hp
  have hs := mul_self_le_mul_self hG hp
  rw [l2Norm,l2Norm,←pow_two,←pow_two,mul_pow,Real.sq_sqrt hE,Real.sq_sqrt hL] at hs
  have hP := parent_boundary_dirichlet_poincare Q u
  change energy Q u.toH1Function.toFun≤C*G at hP
  have hsq : G^2≤(C*energy Q (dirichletWeakLaplacian H))*G :=
    hs.trans (by simpa only [mul_assoc,mul_comm,mul_left_comm] using
      mul_le_mul_of_nonneg_right hP hL)
  by_cases hz : G=0
  · rw [show (∑ i : Fin 2,energy Q (fun x => u.toH1Function.grad x i))=G from rfl,hz]
    exact mul_nonneg (by positivity) hL
  · apply (mul_le_mul_iff_right₀ (lt_of_le_of_ne hG (Ne.symm hz))).1
    convert hsq using 1 <;> ring

end
end ASDExplicitGamma.Native
