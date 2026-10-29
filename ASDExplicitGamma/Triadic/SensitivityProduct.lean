module

public import ASDExplicitGamma.Triadic.PlanarProductPoincare

/-! The explicit product term in the planar coarse-sensitivity estimate. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory

noncomputable section

/-- The scalar planar sensitivity coefficient for a unit skew matrix. -/
def sensitivityB2 : ℝ := Real.sqrt 2 / Real.pi

/-- The Hessian-to-gradient conversion in the source sensitivity estimate. -/
def sensitivityKappaH : ℝ := planarC0 * planarC1 / (2 / Real.pi)

/-- Frobenius-scaled first derivative size of a planar scalar skew field. -/
def sensitivityD1 (Q : TriadicCube 2) (h : PlanarW2Infinity Q) : ℝ :=
  cubeScaleFactor Q * Real.sqrt 2 * planarGradientLInf h

/-- Frobenius-scaled second derivative size of a planar scalar skew field. -/
def sensitivityD2 (Q : TriadicCube 2) (h : PlanarW2Infinity Q) : ℝ :=
  cubeScaleFactor Q ^ 2 * Real.sqrt 2 * planarHessianFrobeniusLInf h

/-- The combined direction size used by coarse sensitivity. -/
def sensitivityDsharp (Q : TriadicCube 2) (h : PlanarW2Infinity Q) : ℝ :=
  sensitivityD1 Q h + sensitivityKappaH * sensitivityD2 Q h

private theorem planarFD_le_two_div_pi : planarFD ≤ 2 / Real.pi := by
  have hleft : 0 ≤ planarFD := by rw [planarFD_exact]; positivity
  have hright : 0 ≤ 2 / Real.pi := by positivity
  apply (sq_le_sq₀ hleft hright).1
  rw [planarFD_exact, div_pow,
    Real.sq_sqrt (show 0 ≤ (7 / 2 : ℝ) by norm_num)]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  norm_num

private theorem planarCD_le_planarC0 : planarCD ≤ planarC0 := by
  have hleft : 0 ≤ planarCD := by unfold planarCD; exact Real.sqrt_nonneg _
  have hright : 0 ≤ planarC0 := by unfold planarC0; exact Real.sqrt_nonneg _
  apply (sq_le_sq₀ hleft hright).1
  rw [planarCD_sq, planarC0_sq_eq_planarC1_sq_add]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hden : 0 < Real.pi ^ 2 := sq_pos_of_ne_zero hpi
  have hrecip : 1 / (2 * Real.pi ^ 2) ≤ 1 / Real.pi ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hden]
    nlinarith [sq_pos_of_ne_zero hpi]
  linarith

private theorem sensitivity_coefficients_nonneg :
    0 ≤ sensitivityB2 ∧ 0 ≤ sensitivityKappaH ∧ 0 ≤ planarC1 := by
  unfold sensitivityB2 sensitivityKappaH
  refine ⟨by positivity, ?_, Real.sqrt_nonneg _⟩
  apply div_nonneg
  · exact mul_nonneg (by unfold planarC0; positivity) (by unfold planarC1; positivity)
  · positivity

/-- The genuine planar product/Poincaré estimate, with its two terms absorbed
by the source Frobenius-scaled `Dsharp` coefficient. -/
theorem sensitivity_product_poincare (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) (h : PlanarW2Infinity Q) :
    vectorPositiveHaarNorm Q
        (fun x i => planarJGradient h x i * u.toH1Function.toFun x) ≤
      sensitivityB2 * sensitivityDsharp Q h *
        vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) := by
  have hprod := planar_product_poincare Q u h
  have hcoeff := sensitivity_coefficients_nonneg
  have hR : 0 ≤ cubeScaleFactor Q := (cubeScaleFactor_pos' Q).le
  have hG : 0 ≤ planarGradientLInf h := by
    unfold planarGradientLInf planarW1ValueLInf
    positivity
  have hH : 0 ≤ planarHessianFrobeniusLInf h := by
    unfold planarHessianFrobeniusLInf planarW1DerivativeFrobeniusLInf
    positivity
  have hFD := planarFD_le_two_div_pi
  have hCD := planarCD_le_planarC0
  have hC1 : 0 ≤ planarC1 := (sensitivity_coefficients_nonneg).2.2
  have hcoef :
      cubeScaleFactor Q * planarFD * planarGradientLInf h +
          cubeScaleFactor Q ^ 2 * planarCD * planarC1 *
            planarHessianFrobeniusLInf h ≤
        sensitivityB2 * sensitivityDsharp Q h := by
    unfold sensitivityB2 sensitivityDsharp sensitivityD1 sensitivityD2
      sensitivityKappaH
    have hCDprod : planarCD * planarC1 ≤ planarC0 * planarC1 :=
      mul_le_mul_of_nonneg_right hCD hC1
    calc
      cubeScaleFactor Q * planarFD * planarGradientLInf h +
          cubeScaleFactor Q ^ 2 * planarCD * planarC1 *
            planarHessianFrobeniusLInf h ≤
        cubeScaleFactor Q * (2 / Real.pi) * planarGradientLInf h +
          cubeScaleFactor Q ^ 2 * planarC0 * planarC1 *
            planarHessianFrobeniusLInf h := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hFD hR) hG
              · calc
                  cubeScaleFactor Q ^ 2 * planarCD * planarC1 *
                      planarHessianFrobeniusLInf h =
                    (cubeScaleFactor Q ^ 2 * (planarCD * planarC1)) *
                      planarHessianFrobeniusLInf h := by ring
                  _ ≤ (cubeScaleFactor Q ^ 2 * (planarC0 * planarC1)) *
                      planarHessianFrobeniusLInf h :=
                    mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hCDprod (sq_nonneg _)) hH
                  _ = cubeScaleFactor Q ^ 2 * planarC0 * planarC1 *
                      planarHessianFrobeniusLInf h := by ring
      _ = sensitivityB2 *
          (cubeScaleFactor Q * Real.sqrt 2 * planarGradientLInf h +
            (planarC0 * planarC1 / (2 / Real.pi)) *
              (cubeScaleFactor Q ^ 2 * Real.sqrt 2 *
                planarHessianFrobeniusLInf h)) := by
              dsimp [sensitivityB2]
              have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
              have hsqrt : (Real.sqrt 2) ^ 2 = 2 :=
                Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
              field_simp [hpi]
              rw [hsqrt]
              ring
  have hweak : 0 ≤ vectorWeakHaarNorm Q
      (fun x i => u.toH1Function.grad x i) := Real.sqrt_nonneg _
  calc
    vectorPositiveHaarNorm Q
        (fun x i => planarJGradient h x i * u.toH1Function.toFun x) ≤
      (cubeScaleFactor Q * planarFD * planarGradientLInf h +
        cubeScaleFactor Q ^ 2 * planarCD * planarC1 *
          planarHessianFrobeniusLInf h) *
        vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) := hprod
    _ ≤ sensitivityB2 * sensitivityDsharp Q h *
        vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) :=
          mul_le_mul_of_nonneg_right hcoef hweak

/-- A mean-zero scalar skew direction has the sharp positive-Haar bound
needed for the constant-load term in the polarized variation. -/
theorem sensitivity_meanZero_positive_bound (Q : TriadicCube 2)
    (h : PlanarW2Infinity Q)
    (hmean : cubeAverage Q h.value.toFun = 0) :
    positiveHaarNorm Q h.value.toFun ≤
      cubeScaleFactor Q * planarC0 * planarGradientLInf h := by
  let G : Vec 2 → Fin 2 → ℝ := fun x i => h.value.grad x i
  have hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q) := by
    intro i
    exact h.value.grad_memL2_normalizedCubeMeasure i
  have hGradEnergy : ∑ i, energy Q (fun x => G x i) ≤
      planarGradientLInf h ^ 2 := by
    have hmul := vectorEnergy_mul_le_linf Q h.gradient
      (f := fun _ : Vec 2 => (1 : ℝ)) (memLp_const (1 : ℝ))
    simpa [G, planarGradientLInf, planarW1Value, h.gradient_eq, energy,
      pairing, cubeAverage_const] using hmul
  have hPoincare := cube_poincare Q h.value.memL2_normalizedCubeMeasure hG
    h.value.hasWeakGradient
  have hEnergy : energy Q h.value.toFun ≤
      (cubeScaleFactor Q / Real.pi) ^ 2 * planarGradientLInf h ^ 2 := by
    have hmeanEq : energy Q h.value.toFun =
        energy Q (fun x => h.value.toFun x - cubeAverage Q h.value.toFun) := by
      rw [hmean]
      simp
    rw [hmeanEq]
    calc
      energy Q (fun x => h.value.toFun x - cubeAverage Q h.value.toFun) ≤
          (cubeScaleFactor Q / Real.pi) ^ 2 * ∑ i, energy Q (fun x => G x i) := by
            simpa [G] using hPoincare
      _ ≤ (cubeScaleFactor Q / Real.pi) ^ 2 * planarGradientLInf h ^ 2 :=
        mul_le_mul_of_nonneg_left hGradEnergy (sq_nonneg _)
  have hpositive := positiveHaarNorm_sq_le_l2_add_gradient Q
    h.value.memL2_normalizedCubeMeasure hG h.value.hasWeakGradient
  have hC0 : planarC0 ^ 2 = planarC1 ^ 2 + 1 / Real.pi ^ 2 :=
    planarC0_sq_eq_planarC1_sq_add
  have hsq : positiveHaarNorm Q h.value.toFun ^ 2 ≤
      (cubeScaleFactor Q * planarC0 * planarGradientLInf h) ^ 2 := by
    calc
      positiveHaarNorm Q h.value.toFun ^ 2 ≤
          energy Q h.value.toFun + cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
            ∑ i, energy Q (fun x => G x i) := hpositive
      _ ≤ (cubeScaleFactor Q / Real.pi) ^ 2 * planarGradientLInf h ^ 2 +
          cubeScaleFactor Q ^ 2 * planarC1 ^ 2 * planarGradientLInf h ^ 2 := by
            apply add_le_add hEnergy
            exact mul_le_mul_of_nonneg_left hGradEnergy
              (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = (cubeScaleFactor Q * planarC0 * planarGradientLInf h) ^ 2 := by
            simp only [div_pow, mul_pow]
            rw [hC0]
            ring
  have hleft : 0 ≤ positiveHaarNorm Q h.value.toFun := Real.sqrt_nonneg _
  have hgradNonneg : 0 ≤ planarGradientLInf h := by
    unfold planarGradientLInf planarW1ValueLInf
    positivity
  have hright : 0 ≤ cubeScaleFactor Q * planarC0 * planarGradientLInf h := by
    exact mul_nonneg (mul_nonneg (cubeScaleFactor_pos' Q).le
      (Real.sqrt_nonneg _)) hgradNonneg
  exact (sq_le_sq₀ hleft hright).1 hsq

end

end ASDExplicitGamma.Triadic
