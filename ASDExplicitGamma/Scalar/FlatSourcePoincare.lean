module

public import ASDExplicitGamma.Triadic.PlanarPositiveGradient
public import ASDExplicitGamma.Triadic.VectorHaar
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.NormNum

/-! The source positive-Haar norm is controlled by actual L² values and weak
gradients, with the finite-cell coefficient used by the flat-source estimate. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory
open ASDExplicitGamma.Triadic
open scoped BigOperators

private theorem planarC1_sq_le_467_sq :
    planarC1 ^ 2 ≤ (467 / 1000 : ℝ) ^ 2 := by
  have hs3 : Real.sqrt 3 < 2 := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hpi : (3 : ℝ) < Real.pi := by linarith [Real.pi_gt_d20]
  have hden : 7 < Real.pi ^ 2 * (1 - Real.sqrt 3 / 9) := by
    have hpiSq : (9 : ℝ) < Real.pi ^ 2 := by nlinarith
    have hfac : (7 / 9 : ℝ) < 1 - Real.sqrt 3 / 9 := by nlinarith
    have hpos : 0 < 1 - Real.sqrt 3 / 9 := by linarith
    calc
      7 = 9 * (7 / 9 : ℝ) := by norm_num
      _ < Real.pi ^ 2 * (1 - Real.sqrt 3 / 9) := by
        exact mul_lt_mul hpiSq hfac.le (by norm_num) (by positivity)
  have hnum : Real.sqrt 3 - 1 < 1 := by linarith
  have hc : planarC1 ^ 2 < (1 / 7 : ℝ) := by
    rw [planarC1_sq]
    apply (div_lt_iff₀ (by linarith)).2
    have hden' : 1 < Real.pi ^ 2 * (1 - Real.sqrt 3 / 9) / 7 := by
      apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 7)).2
      linarith
    nlinarith
  have hrat : (1 / 7 : ℝ) < (467 / 1000 : ℝ) ^ 2 := by norm_num
  exact hc.le.trans hrat.le

/-- The vector-valued positive Haar norm of a genuine H¹ field on a finite
cell is bounded by its normalized L² energy and the weak-gradient energy. -/
theorem vector_positiveHaarNorm_sq_le_l2_add_gradient
    (Q : TriadicCube 2)
    (F : Vec 2 → Fin 2 → ℝ) (G : Vec 2 → Fin 2 → Fin 2 → ℝ)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i j, MemLp (fun x => G x i j) 2 (normalizedCubeMeasure Q))
    (hweak : ∀ i, HasWeakGradientOn (openCubeSet Q) (fun x => F x i)
      (fun x j => G x i j)) :
    vectorPositiveHaarNorm Q F ^ 2 ≤
      (∑ i, energy Q (fun x => F x i)) +
        (467 / 1000 : ℝ) ^ 2 * cubeScaleFactor Q ^ 2 *
          ∑ i, ∑ j, energy Q (fun x => G x i j) := by
  rw [vectorPositiveHaarNorm_sq]
  calc
    ∑ i, positiveHaarNorm Q (fun x => F x i) ^ 2 ≤
        ∑ i, (energy Q (fun x => F x i) +
          cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
            ∑ j, energy Q (fun x => G x i j)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact positiveHaarNorm_sq_le_l2_add_gradient Q (hF i)
        (fun j => hG i j) (hweak i)
    _ = (∑ i, energy Q (fun x => F x i)) +
        cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
          ∑ i, ∑ j, energy Q (fun x => G x i j) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ (∑ i, energy Q (fun x => F x i)) +
        (467 / 1000 : ℝ) ^ 2 * cubeScaleFactor Q ^ 2 *
          ∑ i, ∑ j, energy Q (fun x => G x i j) := by
      have hgrad : 0 ≤ ∑ i, ∑ j, energy Q (fun x => G x i j) :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => energy_nonneg Q _
      apply add_le_add le_rfl
      calc
        cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
            (∑ i, ∑ j, energy Q (fun x => G x i j))
            ≤ cubeScaleFactor Q ^ 2 * (467 / 1000 : ℝ) ^ 2 *
              (∑ i, ∑ j, energy Q (fun x => G x i j)) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left planarC1_sq_le_467_sq
                    (sq_nonneg (cubeScaleFactor Q))) hgrad
        _ = (467 / 1000 : ℝ) ^ 2 * cubeScaleFactor Q ^ 2 *
            (∑ i, ∑ j, energy Q (fun x => G x i j)) := by ring

end ASDExplicitGamma.Scalar
