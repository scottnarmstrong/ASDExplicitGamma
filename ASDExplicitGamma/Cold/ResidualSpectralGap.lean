module

public import ASDExplicitGamma.Cold.ResidualModeAlgebra

/-! # Assembly of the constrained square spectral gap -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic ASDExplicitGamma.Triadic.Torus
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Cold

/-- The spatial axial weight in terms of the squared frequency. -/
theorem residualAxialWeight_expand (i : Fin 2) (p : Fin 2 → ℤ)
    (a : (Fin 2 → ℤ) → ℝ) (s : ℝ) (ha : a p ^ 2 = (p i : ℝ) ^ 2 * s) :
    residualAxialWeight i a p =
      (if (p (Fin.rev i) : ℝ) ^ 2 = 0 ∧ (p i : ℝ) ^ 2 = 1
        then -(p i : ℝ) ^ 2 * s else 0) +
      (if (p (Fin.rev i) : ℝ) ^ 2 = 0 ∧ 9 ≤ (p i : ℝ) ^ 2
        then (7 / 9 : ℝ) * (p i : ℝ) ^ 2 * s else 0) := by
  classical
  have h0 : p (Fin.rev i) = 0 ↔ (p (Fin.rev i) : ℝ) ^ 2 = 0 := by simp
  have h1 : (p i) ^ 2 = 1 ↔ (p i : ℝ) ^ 2 = 1 := by norm_cast
  have h9 : (9 : ℤ) ≤ (p i) ^ 2 ↔ (9 : ℝ) ≤ (p i : ℝ) ^ 2 := by norm_cast
  unfold residualAxialWeight axialBadSet axialHighSet
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, h0, h1, h9, ha]
  split_ifs <;> ring

/-- The modewise comparison uses exactly the zero scalar mean and the weak derivative
coefficient identities, with no additional orthogonality assumptions. -/
theorem residual_spectral_mode_bound (Q : TriadicCube 2)
    (c : (Fin 2 → ℤ) → ℝ) (a : Fin 2 → (Fin 2 → ℤ) → ℝ)
    (hc0 : c 0 = 0) (hcoef : ∀ i p, a i p = -cubeFreq Q p i * c p) (p : Fin 2 → ℤ) :
    (∑ i : Fin 2, residualAxialWeight i (a i) p) ≤
      (∑ i : Fin 2, a i p ^ 2) - 2 * (Real.pi / cubeScaleFactor Q) ^ 2 * c p ^ 2 := by
  let s := (Real.pi / cubeScaleFactor Q) ^ 2 * c p ^ 2
  have hs : 0 ≤ s := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsq (i : Fin 2) : a i p ^ 2 = (p i : ℝ) ^ 2 * s := by
    rw [hcoef]
    unfold cubeFreq s
    ring
  have hzero : (p 0 : ℝ) ^ 2 = 0 → (p 1 : ℝ) ^ 2 = 0 → s = 0 := by
    intro h0 h1
    have hp0 : p 0 = 0 := by simpa only [sq_eq_zero_iff, Int.cast_eq_zero] using h0
    have hp1 : p 1 = 0 := by simpa only [sq_eq_zero_iff, Int.cast_eq_zero] using h1
    have hp : p = 0 := by ext i; fin_cases i; exact hp0; exact hp1
    dsimp only [s]
    rw [hp, hc0]
    ring
  have hgap := residual_mode_gap hs (int_sq_cases_real (p 0)) (int_sq_cases_real (p 1)) hzero
  simp only [Fin.sum_univ_two]
  rw [residualAxialWeight_expand 0 p (a 0) s (hsq 0),
    residualAxialWeight_expand 1 p (a 1) s (hsq 1), hsq 0, hsq 1]
  have hr0 : Fin.rev (0 : Fin 2) = 1 := rfl
  have hr1 : Fin.rev (1 : Fin 2) = 0 := rfl
  rw [hr0, hr1]
  have heq : ((p 0 : ℝ) ^ 2 + (p 1 : ℝ) ^ 2 - 2) * s =
      (p 0 : ℝ) ^ 2 * s + (p 1 : ℝ) ^ 2 * s -
        2 * (Real.pi / cubeScaleFactor Q) ^ 2 * c p ^ 2 := by dsimp [s]; ring
  rw [← heq]
  exact hgap

/-- The squared residual Poincaré estimate in its spectral-gap form. -/
theorem square_residual_spectral_gap (Q : TriadicCube 2) (u : H1Function (openCubeSet Q))
    (hmean : ∫ x, u.toFun x ∂normalizedCubeMeasure Q = 0)
    (hgradmean : ∀ i, ∫ x, u.grad x i ∂normalizedCubeMeasure Q = 0) :
    2 * (Real.pi / cubeScaleFactor Q) ^ 2 *
      (∫ x, u.toFun x ^ 2 ∂normalizedCubeMeasure Q) ≤
      ∑ i : Fin 2, ∫ x, u.grad x i ^ 2 ∂normalizedCubeMeasure Q := by
  let c : (Fin 2 → ℤ) → ℝ := squareScalarCoeff Q ∅ u.toFun
  let a : Fin 2 → (Fin 2 → ℤ) → ℝ := fun i => squareScalarCoeff Q {i} (fun x => u.grad x i)
  have hu := memLp_normalized_of_memL2On u.memL2
  have hG (i : Fin 2) := memLp_normalized_of_memL2On (u.gradMemL2 i)
  have hc : HasSum (fun p => c p ^ 2) (∫ x, u.toFun x ^ 2 ∂normalizedCubeMeasure Q) :=
    square_mixed_parseval Q ∅ hu
  have ha (i : Fin 2) : HasSum (fun p => a i p ^ 2)
      (∫ x, u.grad x i ^ 2 ∂normalizedCubeMeasure Q) := square_mixed_parseval Q {i} (hG i)
  have hc0 : c 0 = 0 := by
    dsimp only [c, squareScalarCoeff]
    simp only [boxMode, Pi.zero_apply, Int.cast_zero, mul_zero, zero_mul, zero_div,
      Real.cos_zero, Real.sin_zero, Finset.notMem_empty, ite_false, Finset.prod_const_one, one_mul]
    exact hmean
  have hcoef (i : Fin 2) (p : Fin 2 → ℤ) : a i p = -cubeFreq Q p i * c p :=
    h1_sine_derivative_coefficient Q u i p
  let W (i : Fin 2) := -2 * a i (axialFirst i 1) ^ 2 + (7 / 9 : ℝ) *
    ∑' p, (axialHighSet i).indicator (fun q => a i q ^ 2) p
  have hw (i : Fin 2) : HasSum (residualAxialWeight i (a i)) (W i) :=
    residualAxialWeight_hasSum i (a i) (ha i).summable
      (squareScalarCoeff_neg_first Q i (fun x => u.grad x i))
  have hW (i : Fin 2) : 0 ≤ W i := by
    have hbound := residual_axial_bound Q i (hG i) (hgradmean i)
    have hnonneg : 0 ≤ ∑' p, (axialHighSet i).indicator (fun q => a i q ^ 2) p :=
      tsum_nonneg (fun p => Set.indicator_nonneg (fun _ _ => sq_nonneg _) p)
    dsimp only [W]
    change 6 * a i (axialFirst i 1) ^ 2 ≤ _ at hbound
    linarith only [hbound, hnonneg]
  have hsumW := hasSum_sum (s := Finset.univ) (fun i _ => hw i)
  have hsumD := (hasSum_sum (s := Finset.univ) (fun i _ => ha i)).sub
    (hc.mul_left (2 * (Real.pi / cubeScaleFactor Q) ^ 2))
  have hle := hasSum_le (residual_spectral_mode_bound Q c a hc0 hcoef) hsumW hsumD
  have hnonneg : 0 ≤ ∑ i : Fin 2, W i := Finset.sum_nonneg (fun i _ => hW i)
  linarith only [hle, hnonneg]

end ASDExplicitGamma.Cold
