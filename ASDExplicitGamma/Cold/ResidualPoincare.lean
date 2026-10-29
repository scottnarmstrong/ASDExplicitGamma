module

public import ASDExplicitGamma.Cold.ResidualSpectralGap

/-! # The source residual Poincaré constant on the square -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Cold

/-- CO-PLATEAU-RESIDUAL-POINCARE, with the square's side length included.
For the unit square this is exactly `1/(√2 π)`. Both source constraints are spatial
means, and the derivatives are the actual weak gradient of the H¹ function. -/
theorem square_residual_poincare (Q : TriadicCube 2) (u : H1Function (openCubeSet Q))
    (hmean : ∫ x, u.toFun x ∂normalizedCubeMeasure Q = 0)
    (hgradmean : ∀ i, ∫ x, u.grad x i ∂normalizedCubeMeasure Q = 0) :
    Real.sqrt (∫ x, u.toFun x ^ 2 ∂normalizedCubeMeasure Q) ≤
      (cubeScaleFactor Q / (Real.sqrt 2 * Real.pi)) *
        Real.sqrt (∑ i : Fin 2, ∫ x, u.grad x i ^ 2 ∂normalizedCubeMeasure Q) := by
  have hgap := square_residual_spectral_gap Q u hmean hgradmean
  have hℓ := cubeScaleFactor_pos' Q
  have he : 0 ≤ ∑ i : Fin 2, ∫ x, u.grad x i ^ 2 ∂normalizedCubeMeasure Q :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hq : 0 < 2 * (Real.pi / cubeScaleFactor Q) ^ 2 := by positivity
  have hroot : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have heq : 1 / (2 * (Real.pi / cubeScaleFactor Q) ^ 2) =
      (cubeScaleFactor Q / (Real.sqrt 2 * Real.pi)) ^ 2 := by
    field_simp
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsquared : (∫ x, u.toFun x ^ 2 ∂normalizedCubeMeasure Q) ≤
      (cubeScaleFactor Q / (Real.sqrt 2 * Real.pi)) ^ 2 *
        (∑ i : Fin 2, ∫ x, u.grad x i ^ 2 ∂normalizedCubeMeasure Q) := by
    calc
      _ ≤ (∑ i : Fin 2, ∫ x, u.grad x i ^ 2 ∂normalizedCubeMeasure Q) /
          (2 * (Real.pi / cubeScaleFactor Q) ^ 2) := by
        apply (le_div_iff₀ hq).mpr
        simpa only [mul_comm] using hgap
      _ = _ := by
        simp only [one_div] at heq
        rw [div_eq_mul_inv, heq]
        ring
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · rw [mul_pow, Real.sq_sqrt he]
    exact hsquared

end ASDExplicitGamma.Cold
