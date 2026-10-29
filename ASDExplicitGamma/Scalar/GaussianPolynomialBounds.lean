module

public import ASDExplicitGamma.Gaussian.FiniteProduct
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Polynomial growth and integration by parts for Gaussian coordinate monomials. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory
open ASDExplicitGamma.Gaussian

/-- Coordinate differentiation obeys the ordinary product rule. -/
theorem gaussian_coordinate_derivative_mul {n : ℕ} {F G : (Fin n → ℝ) → ℝ}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (i : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative (fun y => F y*G y) i x =
      coordinateDerivative F i x*G x+F x*coordinateDerivative G i x := by
  have h := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i 1))
    (fderiv_fun_mul (hF x) (hG x))
  simpa only [coordinateDerivative,add_apply,smul_apply,
    smul_eq_mul,mul_comm,add_comm] using h

/-- Product closure keeps a common polynomial bound for every coordinate derivative. -/
theorem gaussian_polynomial_bound_mul {n : ℕ} {F G : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F)
    (hG : HasPolynomiallyBoundedCoordinateDerivatives G) :
    HasPolynomiallyBoundedCoordinateDerivatives (fun x => F x*G x) := by
  obtain ⟨hFc,CF,hCF,dF,hF0,hF1⟩ := hF
  obtain ⟨hGc,CG,hCG,dG,hG0,hG1⟩ := hG
  refine ⟨hFc.mul hGc,CF*CG,mul_nonneg hCF hCG,dF+dG,?_,?_⟩
  · intro x
    rw [abs_mul,pow_add]
    have h := mul_le_mul (hF0 x) (hG0 x) (abs_nonneg _) (mul_nonneg hCF (by positivity))
    convert h using 1
    ring
  · intro i x
    rw [gaussian_coordinate_derivative_mul (hFc.differentiable (by norm_num))
      (hGc.differentiable (by norm_num)),abs_mul,pow_add]
    have hprod := mul_le_mul (hF1 i x) (hG1 i x)
      (add_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hCF (by positivity))
    have habs := abs_add_le (coordinateDerivative F i x*G x) (F x*coordinateDerivative G i x)
    rw [abs_mul,abs_mul] at habs
    have hnn := mul_nonneg (abs_nonneg (coordinateDerivative F i x))
      (abs_nonneg (coordinateDerivative G i x))
    nlinarith only [hprod,habs,hnn]

/-- Evaluation in a coordinate has linear growth and a constant derivative. -/
theorem gaussian_polynomial_bound_eval {n : ℕ} (j : Fin n) :
    HasPolynomiallyBoundedCoordinateDerivatives (fun x : Fin n → ℝ => x j) := by
  have hd (i : Fin n) (x : Fin n → ℝ) :
      coordinateDerivative (fun y : Fin n → ℝ => y j) i x = if j=i then 1 else 0 := by
    unfold coordinateDerivative
    rw [(hasFDerivAt_apply j x).fderiv]
    simp only [ContinuousLinearMap.proj_apply,Pi.single_apply]
  refine ⟨by fun_prop,1,by norm_num,1,?_,?_⟩
  · intro x
    have h := norm_le_pi_norm x j
    simpa only [Real.norm_eq_abs,one_mul,pow_one] using h.trans (le_add_of_nonneg_left zero_le_one)
  · intro i x
    rw [hd]
    have h := norm_le_pi_norm x j
    simp only [Real.norm_eq_abs] at h
    split_ifs <;> simp only [abs_one,abs_zero,pow_one,one_mul] <;> linarith only [h]

noncomputable def gaussianMonomial {n : ℕ} (a : List (Fin n)) (x : Fin n → ℝ) : ℝ :=
  (a.map (fun i => x i)).prod

/-- Every coordinate monomial meets the existing Gaussian integration-by-parts growth contract. -/
theorem gaussian_monomial_coordinate_bound {n : ℕ} (a : List (Fin n)) :
    HasPolynomiallyBoundedCoordinateDerivatives (gaussianMonomial a) := by
  induction a with
  | nil =>
    have he : gaussianMonomial ([] : List (Fin n)) = fun _ => (1:ℝ) := by
      funext x
      rfl
    rw [he]
    refine ⟨contDiff_const,1,by norm_num,0,?_,?_⟩
    · intro x
      norm_num [gaussianMonomial]
    · intro i x
      norm_num [coordinateDerivative]
  | cons j a ih =>
    exact gaussian_polynomial_bound_mul (gaussian_polynomial_bound_eval j) ih

/-- The genuine monomial integral has no integrability premise left over. -/
theorem integrable_gaussian_monomial {n : ℕ} (a : List (Fin n)) :
    Integrable (gaussianMonomial a) (standardGaussianPi n) := by
  obtain ⟨hc,C,hC,d,h0,_⟩ := gaussian_monomial_coordinate_bound a
  exact integrable_of_pi_polynomial_bound hc.continuous.measurable hC h0

end ASDExplicitGamma.Scalar
