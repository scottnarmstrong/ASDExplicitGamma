module

public import ASDExplicitGamma.Triadic.DiagCellPolynomial
public import ASDExplicitGamma.Triadic.DiagCertificates

/-! Cellwise positive-Haar bounds in exact centered polynomial coefficients. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

theorem diagBilinearPolynomial_energy_explicit (Q : TriadicCube 2) (c : Fin 4 → ℝ) :
    energy Q (diagBilinearPolynomial Q c) =
      c 0 ^ 2 + c 1 ^ 2 / 12 + c 2 ^ 2 / 12 + c 3 ^ 2 / 144 := by
  rw [diagBilinearPolynomial_energy]
  simp [diagBilinearWeight, Fin.sum_univ_succ]
  ring

/-- Coefficients of the first or second physical derivative. -/
def diagBilinearDerivativeCoefficients (Q : TriadicCube 2) (c : Fin 4 → ℝ) (i : Fin 2) : Fin 4 → ℝ :=
  if i = 0 then ![c 1 / cubeScaleFactor Q, 0, c 3 / cubeScaleFactor Q, 0]
    else ![c 2 / cubeScaleFactor Q, c 3 / cubeScaleFactor Q, 0, 0]

theorem diagBilinearH1_grad_polynomial (Q : TriadicCube 2) (c : Fin 4 → ℝ) (i : Fin 2) :
    (fun x => (diagBilinearH1 Q c).grad x i) =
      diagBilinearPolynomial Q (diagBilinearDerivativeCoefficients Q c i) := by
  funext x
  rw [diagBilinearH1_grad, diagBilinearPolynomial_explicit]
  fin_cases i <;> simp [diagBilinearDerivativeCoefficients] <;> ring

/-- Every H¹ cell has a finite positive series and the sharp full positive-norm bound. -/
theorem diagPrimalEnergy_le_l2_add_gradient (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) :
    primalEnergy Q (Real.sqrt 3) u.toFun ≤ energy Q u.toFun +
      cubeScaleFactor Q ^ 2 * planarC1 ^ 2 * ∑ i, energy Q (fun x => u.grad x i) := by
  have h := positiveHaarNorm_sq_le_l2_add_gradient Q u.memL2_normalizedCubeMeasure
    u.grad_memL2_normalizedCubeMeasure u.hasWeakGradient
  rw [positiveHaarNorm, Real.sq_sqrt (primalEnergy_nonneg Q (Real.sqrt 3)
    (Real.sqrt_nonneg 3) u.toFun)] at h
  exact h

theorem diagBilinearH1_gradient_energy (Q : TriadicCube 2) (c : Fin 4 → ℝ) :
    (∑ i, energy Q (fun x => (diagBilinearH1 Q c).grad x i)) =
      (c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2 / 6) / cubeScaleFactor Q ^ 2 := by
  simp only [diagBilinearH1_grad_polynomial, diagBilinearPolynomial_energy_explicit,
    Fin.sum_univ_two, diagBilinearDerivativeCoefficients]
  norm_num
  ring

/-- Cell positive energy uses the exact L² moments and the rational enclosure. -/
theorem diagBilinearPolynomial_positive_le (Q : TriadicCube 2) (c : Fin 4 → ℝ) :
    primalEnergy Q (Real.sqrt 3) (diagBilinearPolynomial Q c) ≤
      c 0 ^ 2 + c 1 ^ 2 / 12 + c 2 ^ 2 / 12 + c 3 ^ 2 / 144 +
      (c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2 / 6) / 10 := by
  have h := diagPrimalEnergy_le_l2_add_gradient Q (diagBilinearH1 Q c)
  rw [diagBilinearH1_toFun, diagBilinearPolynomial_energy_explicit,
    diagBilinearH1_gradient_energy] at h
  have hc := diagPlanarC1_sq_lt_tenth.le
  have hnonneg : 0 ≤ c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2 / 6 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hc hnonneg
  have hcancel : cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
      ((c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2 / 6) / cubeScaleFactor Q ^ 2) =
      planarC1 ^ 2 * (c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2 / 6) := by
    field_simp [(cubeScaleFactor_pos' Q).ne']
  rw [hcancel] at h
  linarith only [h, hmul]

/-- Positive energy of a derivative uses its transverse centered variance. -/
theorem diagBilinearPolynomial_derivative_positive_le (Q : TriadicCube 2) (c : Fin 4 → ℝ)
    (i : Fin 2) :
    primalEnergy Q (Real.sqrt 3) (fun x => (diagBilinearH1 Q c).grad x i) ≤
      ((if i = 0 then c 1 ^ 2 else c 2 ^ 2) + (11/60:ℝ)*c 3 ^ 2) / cubeScaleFactor Q ^ 2 := by
  rw [diagBilinearH1_grad_polynomial]
  have h := diagBilinearPolynomial_positive_le Q (diagBilinearDerivativeCoefficients Q c i)
  fin_cases i <;> simp only [diagBilinearDerivativeCoefficients, Fin.isValue] at h ⊢ <;> norm_num at h ⊢ <;> convert h using 1 <;> ring

end

end ASDExplicitGamma.Triadic
