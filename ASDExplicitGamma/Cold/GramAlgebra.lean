module

public import ASDExplicitGamma.Cold.EigenvalueOrder
public import Mathlib.Analysis.InnerProductSpace.Positive

/-! # Sharp scalar and spectral constants for the plateau Gram bound -/

@[expose] public section
open scoped RealInnerProductSpace
namespace ASDExplicitGamma.Cold

/-- Scalar near-identity bound from reciprocal coercivity. -/
theorem gram_scalar_eigenvalue_le {lambda h : ℝ} (hlambda : 0 < lambda) (hh : 0 ≤ h)
    (hbound : lambda + lambda⁻¹ ≤ 2 * (1 + h)) : lambda ≤ 1 + 2*h + Real.sqrt (2*h) := by
  have hp := mul_le_mul_of_nonneg_right hbound hlambda.le
  rw [add_mul, inv_mul_cancel₀ hlambda.ne'] at hp
  have hs := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hh)
  have hr := Real.sqrt_nonneg (2*h)
  by_contra hn
  have hn' : 1 + 2*h + Real.sqrt (2*h) < lambda := lt_of_not_ge hn
  have hprod := mul_pos (by linarith : 0 < lambda - 1 - 2*h - Real.sqrt (2*h))
    (by linarith : 0 < lambda - 1 + Real.sqrt (2*h))
  nlinarith only [hp, hprod, hs, mul_nonneg hh hr]

/-- The exact source free Young parameter. -/
theorem gram_sqrt_young {η h : ℝ} (hη : 0 < η) (hh : 0 ≤ h) :
    Real.sqrt (2*h) ≤ 2*η + h / (4*η) := by
  have hs := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hh)
  rw [show 2*η + h / (4*η) = (8*η^2+h) / (4*η) by field_simp; ring]
  apply (le_div_iff₀ (by positivity : 0 < 4*η)).mpr
  nlinarith only [sq_nonneg (Real.sqrt (2*h) - 4*η), hs]

/-- Reciprocal coercivity pays the exact source Gram coefficient. -/
theorem gram_scalar_coefficient_le {lambda h η : ℝ} (hlambda : 0 < lambda) (hh : 0 ≤ h) (hη : 0 < η)
    (hbound : lambda + lambda⁻¹ ≤ 2 * (1+h)) :
    lambda + 1 ≤ 2*(1+η) + (2 + 1/(4*η))*h := by
  have h1 := gram_scalar_eigenvalue_le hlambda hh hbound
  have h2 := gram_sqrt_young hη hh
  have heq : 2*(1+η) + (2 + 1/(4*η))*h = 2 + 2*h + (2*η + h/(4*η)) := by ring
  rw [heq]
  linarith only [h1, h2]

/-- An actual symmetric positive operator with inverse coercivity obeys the Gram bound.
The inverse and quadratic hypotheses are internal linear-algebra interfaces. -/
theorem gram_operator_quadratic_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (T S : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (hpos : ∀ x, x ≠ 0 → 0 < ⟪x, T x⟫)
    (hST : ∀ x, S (T x) = x) {h η : ℝ} (hh : 0 ≤ h) (hη : 0 < η)
    (hbound : ∀ x, ⟪x, T x + S x⟫ ≤ 2*(1+h)*⟪x,x⟫) (x : E) :
    ⟪x, T x⟫ + ⟪x,x⟫ ≤ (2*(1+η) + (2+1/(4*η))*h) * ⟪x,x⟫ := by
  let N := Module.finrank ℝ E
  let b := hT.eigenvectorBasis (show Module.finrank ℝ E = N from rfl)
  let lambda := hT.eigenvalues (show Module.finrank ℝ E = N from rfl)
  have heigen (i : Fin N) : T (b i) = lambda i • b i := hT.apply_eigenvectorBasis rfl i
  have hlambda (i : Fin N) : 0 < lambda i := by
    have hp := hpos (b i) (b.orthonormal.ne_zero i)
    rw [heigen, inner_smul_right] at hp
    exact pos_of_mul_pos_left hp real_inner_self_nonneg
  have hinv (i : Fin N) : S (b i) = (lambda i)⁻¹ • b i := by
    have hs := congrArg S (heigen i)
    rw [hST, map_smul] at hs
    calc
      S (b i) = (lambda i)⁻¹ • (lambda i • S (b i)) := by
        rw [smul_smul, inv_mul_cancel₀ (hlambda i).ne', one_smul]
      _ = _ := congrArg ((lambda i)⁻¹ • ·) hs.symm
  have hc (i : Fin N) : lambda i + 1 ≤ 2*(1+η) + (2+1/(4*η))*h := by
    have hi := hbound (b i)
    rw [heigen, hinv, inner_add_right, inner_smul_right, inner_smul_right] at hi
    have hnorm : ⟪b i, b i⟫ = 1 := by rw [real_inner_self_eq_norm_sq, b.norm_eq_one]; norm_num
    rw [hnorm] at hi
    simp only [mul_one] at hi
    exact gram_scalar_coefficient_le (hlambda i) hh hη hi
  rw [inner_apply_eq_eigenbasis_sum b T lambda heigen x, ← eigenbasis_sum_sq_eq_inner b x,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  convert mul_le_mul_of_nonneg_right (hc i) (sq_nonneg (b.repr x i)) using 1
  ring

end ASDExplicitGamma.Cold
