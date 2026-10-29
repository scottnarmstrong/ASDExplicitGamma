module

public import ASDExplicitGamma.Triadic.DiagStencil

/-! Adjoint pairing and positivity of exact Laurent squares on a finite period. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open scoped BigOperators

noncomputable section

/-- The counting-measure pairing of a Laurent stencil and its reversed lags. -/
theorem diagStencilAction_pairing {G : Type*} [AddCommGroup G] [Fintype G]
    (φ : (ℤ × ℤ) →+ G) (p : DiagStencil) (f h : G → ℝ) :
    (∑ x, diagStencilAction φ p f x * h x) =
      ∑ x, f x * diagStencilAction φ (diagStencilAdjoint p) h x := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
      simpa only [map_add, LinearMap.add_apply, Pi.add_apply, add_mul, mul_add,
        Finset.sum_add_distrib] using congrArg₂ (· + ·) hp hq
  | single g c =>
      have hadj : diagStencilAdjoint (AddMonoidAlgebra.single g c) =
          AddMonoidAlgebra.single (-g) c := by
        simp [diagStencilAdjoint]
      rw [hadj]
      simp_rw [diagStencilAction_single, Rat.smul_def]
      have hshift := diagLattice_shift_pairing (Equiv.addRight (φ g)) f h
      have hs : (∑ x, f (x + φ g) * h x) = ∑ x, f x * h (x + φ (-g)) := by
        simpa only [Equiv.coe_addRight, Equiv.addRight_symm_apply, map_neg, sub_eq_add_neg] using hshift
      calc
        _ = (c : ℝ) * ∑ x, f (x + φ g) * h x := by
          rw [Finset.mul_sum]
          congr 1
          funext x
          ring
        _ = (c : ℝ) * ∑ x, f x * h (x + φ (-g)) := congrArg ((c : ℝ) * ·) hs
        _ = _ := by
          rw [Finset.mul_sum]
          congr 1
          funext x
          ring

/-- The quadratic form of a stencil with counting measure. -/
def diagStencilQuadratic {G : Type*} [AddCommGroup G] [Fintype G]
    (φ : (ℤ × ℤ) →+ G) (p : DiagStencil) (f : G → ℝ) : ℝ :=
  ∑ x, f x * diagStencilAction φ p f x

@[simp] theorem diagStencilQuadratic_add {G : Type*} [AddCommGroup G] [Fintype G]
    (φ : (ℤ × ℤ) →+ G) (p q : DiagStencil) (f : G → ℝ) :
    diagStencilQuadratic φ (p + q) f =
      diagStencilQuadratic φ p f + diagStencilQuadratic φ q f := by
  simp only [diagStencilQuadratic, map_add, LinearMap.add_apply, Pi.add_apply,
    mul_add, Finset.sum_add_distrib]

@[simp] theorem diagStencilQuadratic_sub {G : Type*} [AddCommGroup G] [Fintype G]
    (φ : (ℤ × ℤ) →+ G) (p q : DiagStencil) (f : G → ℝ) :
    diagStencilQuadratic φ (p - q) f =
      diagStencilQuadratic φ p f - diagStencilQuadratic φ q f := by
  simp only [diagStencilQuadratic, map_sub, LinearMap.sub_apply, Pi.sub_apply,
    mul_sub, Finset.sum_sub_distrib]

@[simp] theorem diagStencilQuadratic_smul {G : Type*} [AddCommGroup G] [Fintype G]
    (φ : (ℤ × ℤ) →+ G) (c : ℚ) (p : DiagStencil) (f : G → ℝ) :
    diagStencilQuadratic φ (c • p) f = (c : ℝ) * diagStencilQuadratic φ p f := by
  simp only [diagStencilQuadratic, map_smul, LinearMap.smul_apply, Pi.smul_apply,
    Rat.smul_def, Finset.mul_sum]
  congr 1
  funext x
  ring

/-- A Laurent square is an actual sum of squared filtered values. -/
theorem diagStencilQuadratic_square {G : Type*} [AddCommGroup G] [Fintype G]
    (φ : (ℤ × ℤ) →+ G) (p : DiagStencil) (f : G → ℝ) :
    diagStencilQuadratic φ (diagStencilAdjoint p * p) f =
      ∑ x, diagStencilAction φ p f x ^ 2 := by
  have hp := diagStencilAction_pairing φ p f (diagStencilAction φ p f)
  simpa only [diagStencilQuadratic, map_mul, Module.End.mul_apply, pow_two] using hp.symm

/-- Positivity is proved by squares, independently of Fourier normalization. -/
theorem diagStencilQuadratic_square_nonneg {G : Type*} [AddCommGroup G] [Fintype G]
    (φ : (ℤ × ℤ) →+ G) (p : DiagStencil) (f : G → ℝ) :
    0 ≤ diagStencilQuadratic φ (diagStencilAdjoint p * p) f := by
  rw [diagStencilQuadratic_square]
  exact Finset.sum_nonneg fun x _ => sq_nonneg _

end

end ASDExplicitGamma.Triadic
