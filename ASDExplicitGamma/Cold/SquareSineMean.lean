module

public import ASDExplicitGamma.Cold.SquareParsevalPairing
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The constant function in the square's mixed sine/cosine basis -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic ASDExplicitGamma.Triadic.Torus
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Cold

/-- The normalized integral of a sine on an interval, valid also at frequency zero. -/
theorem integral_sin_seg (a : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℤ) :
    ∫ t, Real.sin (Real.pi * m * (t - a) / ℓ) ∂segMeasure a ℓ =
      (1 - Real.cos ((m : ℝ) * Real.pi)) / (Real.pi * m) := by
  by_cases hm : m = 0
  · subst m; simp
  have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hπm : Real.pi * (m : ℝ) ≠ 0 := mul_ne_zero Real.pi_ne_zero hm'
  rw [integral_segMeasure a hℓ]
  have hd (t : ℝ) : HasDerivAt
      (fun s => -(ℓ / (Real.pi * m)) * Real.cos (Real.pi * m * (s - a) / ℓ))
      (Real.sin (Real.pi * m * (t - a) / ℓ)) t := by
    have ht := (((hasDerivAt_id t).sub_const a).const_mul (Real.pi * m)).div_const ℓ
    have hc := ((Real.hasDerivAt_cos _).comp t ht).const_mul (-(ℓ / (Real.pi * m)))
    exact hc.congr_deriv (by dsimp; field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((by fun_prop : Continuous (fun t => Real.sin (Real.pi * m * (t - a) / ℓ))).intervalIntegrable _ _)]
  have he : Real.pi * m * (a + ℓ - a) / ℓ = (m : ℝ) * Real.pi := by
    field_simp; ring
  rw [he]
  simp only [sub_self, mul_zero, zero_div, Real.cos_zero, mul_one]
  field_simp
  ring

/-- The normalized integral of a single mode factor. -/
theorem integral_modeFactor_mean {d : ℕ} (a : Fin d → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (O : Finset (Fin d)) (p : Fin d → ℤ) (i : Fin d) :
    ∫ t, modeFactor a ℓ O p i t ∂segMeasure (a i) ℓ =
      if i ∈ O then (1 - Real.cos ((p i : ℝ) * Real.pi)) / (Real.pi * p i)
      else if p i = 0 then 1 else 0 := by
  by_cases hi : i ∈ O
  · rw [modeFactor_of_mem a ℓ p hi, ite_eq_left hi, integral_sin_seg _ hℓ]
  · rw [modeFactor_of_notMem a ℓ p hi, ite_eq_right hi, integral_cos_seg _ hℓ]

/-- The constant coefficient profile of the basis with sine in coordinate `i`. -/
def squareSineMean (Q : TriadicCube 2) (i : Fin 2) (p : Fin 2 → ℤ) : ℝ :=
  squareScalarCoeff Q {i} (fun _ => 1) p

/-- The constant profile is supported on the corresponding coordinate axis. -/
theorem squareSineMean_formula (Q : TriadicCube 2) (i : Fin 2) (p : Fin 2 → ℤ) :
    squareSineMean Q i p =
      ((1 - Real.cos ((p i : ℝ) * Real.pi)) / (Real.pi * p i)) *
        (if p (Fin.rev i) = 0 then 1 else 0) := by
  unfold squareSineMean squareScalarCoeff
  simp only [mul_one]
  rw [← boxMeasure_eq_normalizedCubeMeasure]
  change (∫ x, ∏ j, modeFactor (cubeCorner Q) (cubeScaleFactor Q) {i} p j (x j)
    ∂boxMeasure (cubeCorner Q) (cubeScaleFactor Q)) = _
  rw [boxMeasure_eq_pi, integral_fintype_prod_eq_prod]
  simp_rw [integral_modeFactor_mean _ (cubeScaleFactor_pos' Q)]
  fin_cases i <;> simp [Fin.prod_univ_two, mul_comm]

end ASDExplicitGamma.Cold
