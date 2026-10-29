module

public import ASDExplicitGamma.Triadic.PlanarDirectionLinear

/-! Literal scalar multiplication and zero planar Sobolev directions. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped ENNReal BigOperators
noncomputable section

 def PlanarW2Infinity.zero (Q : TriadicCube 2) : PlanarW2Infinity Q where
  value := 0
  value_memLp_top := MemLp.zero
  gradient := {
    component := fun _ => 0
    component_memLp_top := fun _ => MemLp.zero
    derivative_memLp_top := fun _ _ => MemLp.zero }
  gradient_eq _ := rfl

 def PlanarW2Infinity.smul {Q : TriadicCube 2} (a : ℝ) (η : PlanarW2Infinity Q) : PlanarW2Infinity Q where
  value := a • η.value
  value_memLp_top := η.value_memLp_top.const_mul a
  gradient := {
    component := fun i => a • η.gradient.component i
    component_memLp_top := fun i => (η.gradient.component_memLp_top i).const_mul a
    derivative_memLp_top := fun i j => by
      simpa only [H1Function.smul_grad, Pi.smul_apply, smul_eq_mul] using (η.gradient.derivative_memLp_top i j).const_mul a }
  gradient_eq i := by
    simp only [H1Function.smul_toFun, H1Function.smul_grad, η.gradient_eq, Pi.smul_apply, smul_eq_mul]

 theorem planarEuclideanNorm_const_mul (a : ℝ) (v : Fin 2 → ℝ) :
    planarEuclideanNorm (fun i => a*v i) = |a| *planarEuclideanNorm v := by
  unfold planarEuclideanNorm
  simp only [mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

 theorem planarFrobeniusNorm_const_mul (a : ℝ) (A : Fin 2 → Fin 2 → ℝ) :
    planarFrobeniusNorm (fun i j => a*A i j) = |a| *planarFrobeniusNorm A := by
  unfold planarFrobeniusNorm
  simp only [mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

end
end ASDExplicitGamma.Triadic
