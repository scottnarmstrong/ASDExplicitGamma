module

public import ASDExplicitGamma.Scalar.OldHessianTrialPositiveRestriction
public import ASDExplicitGamma.Triadic.PlanarDirichletBridge
public import ASDExplicitGamma.Scalar.InverseHistoryLambda

/-! The exact cell-zero weak-energy shift for the genuine coarse potentials.
The root coefficient vanishes before the all-depth series is shifted. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Triadic
noncomputable section

/-- The reciprocal positive-energy identity gives the exact all-depth weak
shift when the actual root mean vanishes. -/
theorem old_hessian_zero_mean_weak_child_shift (Q : TriadicCube 2)
    {q : ℝ} (hq : 1<q) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hmean : cubeAverage Q f=0) :
    dualEnergy Q q f=q⁻¹*descendantsAverage Q 1 (fun U => dualEnergy U q f) := by
  have hh := old_hessian_primal_child_identity Q
    (inv_pos.mpr (zero_lt_one.trans hq)) hf (summable_dual_increments Q hq hf)
  simpa only [dualEnergy,energy_projection_zero,hmean,zero_pow (by norm_num : (2:ℕ)≠0),
    mul_zero,add_zero] using hh

/-- The two-coordinate weak norm inherits the shift without a dimension
factor and without a finite-depth truncation. -/
theorem old_hessian_zero_mean_vector_weak_shift {m : ℕ}
    (Q : TriadicCube 2) (F : Vec 2 → Fin m → ℝ)
    (hF : ∀ i,MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hmean : ∀ i,cubeAverage Q (fun x => F x i)=0) :
    vectorWeakHaarEnergy Q F=(Real.sqrt 3)⁻¹*
      descendantsAverage Q 1 (fun U => vectorWeakHaarEnergy U F) := by
  have hq : (1:ℝ)<Real.sqrt 3 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1)
      (by norm_num : (1:ℝ)<3)
  unfold vectorWeakHaarEnergy
  simp_rw [old_hessian_zero_mean_weak_child_shift Q hq (hF _) (hmean _)]
  rw [←Finset.mul_sum,←Homogenization.descendantsAverage_sum]

/-- The intrinsic quarter-discount squared is precisely the weak Haar
weight. This is the source's alpha², not a rounded replacement. -/
theorem old_hessian_discount_square : (Real.sqrt 3)⁻¹=inverseHistoryDiscount^2 := by
  have hb : sourceHaarBase^2=Real.sqrt 3 := by
    rw [sourceHaarBase,Real.sqrt_eq_rpow,←Real.rpow_natCast,
      ←Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
    congr 1
    norm_num
  have hh := congrArg (fun z : ℝ => z⁻¹) hb
  have hi : sourceHaarBase⁻¹=inverseHistoryDiscount := inverse_history_discount_eq.symm
  rw [←inv_pow,hi] at hh
  exact hh.symm

/-- A genuine cell-zero first potential has exactly the alpha² improvement
in the complete coarse-to-fine weak-energy comparison. -/
theorem old_hessian_h10_weak_shift (Q : TriadicCube 2)
    (phi : H10Function (openCubeSet Q)) :
    vectorWeakHaarEnergy Q phi.toH1Function.grad=inverseHistoryDiscount^2*
      descendantsAverage Q 1 (fun U => vectorWeakHaarEnergy U phi.toH1Function.grad) := by
  rw [←old_hessian_discount_square]
  exact old_hessian_zero_mean_vector_weak_shift Q phi.toH1Function.grad
    phi.toH1Function.grad_memL2_normalizedCubeMeasure
    (cubeAverage_h10_gradient_eq_zero Q phi)

/-- Any finite family of genuine coarse cell-zero potentials has the same
sharp complete shift; in particular the two bottom loads share alpha². -/
theorem old_hessian_h10_family_weak_shift {I : Type*} [Fintype I]
    (Q : TriadicCube 2) (phi : I → H10Function (openCubeSet Q)) :
    (∑ i,vectorWeakHaarEnergy Q (phi i).toH1Function.grad)=inverseHistoryDiscount^2*
      descendantsAverage Q 1 (fun U => ∑ i,vectorWeakHaarEnergy U (phi i).toH1Function.grad) := by
  classical
  simp_rw [old_hessian_h10_weak_shift]
  rw [←Finset.mul_sum,←Homogenization.descendantsAverage_sum]

end
end ASDExplicitGamma.Scalar
