module

public import ASDExplicitGamma.Scalar.GaussianWick
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! The source covariance estimate for finite quadratic Gaussian defects. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory ProbabilityTheory ASDExplicitGamma.Gaussian
open scoped BigOperators RealInnerProductSpace

/-- The finite quadratic defect source with deterministic coefficient family `B`. -/
noncomputable def defectSource {n : ℕ} {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℝ P] (B : Fin n → Fin n → P) (x : Fin n → ℝ) : P :=
  ∑ i, ∑ j, (x i * x j) • B i j

/-- The actual fourth coordinate moment of the standard product Gaussian. -/
theorem standardGaussian_fourth_coordinate_moment {n : ℕ} (i j k l : Fin n) :
    (∫ x, x i * x j * (x k * x l) ∂standardGaussianPi n) =
      (if i = j ∧ k = l then 1 else 0) +
      (if i = k ∧ j = l then 1 else 0) +
      (if i = l ∧ j = k then 1 else 0) := by
  have he : (fun x : Fin n → ℝ => x i * x j * (x k * x l)) =
      gaussianMonomial [i,j,k,l] := by
    funext x
    simp [gaussianMonomial]
    ring
  rw [he, gaussian_integral_eq_wick_value 4 [i,j,k,l] (by simp)]
  by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hil : i = l <;>
    by_cases hjk : j = k <;> by_cases hjl : j = l <;> by_cases hkl : k = l <;>
    simp_all [gaussianWickValue, gaussianContractions]; norm_num

private theorem defectSource_norm_sq_expansion {n : ℕ} {P : Type*}
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] (B : Fin n → Fin n → P)
    (x : Fin n → ℝ) :
    ‖defectSource B x‖ ^ 2 =
      ∑ i, ∑ j, ∑ k, ∑ l,
        inner ℝ (B i j) (B k l) * (x i * x j * (x k * x l)) := by
  rw [← real_inner_self_eq_norm_sq, defectSource]
  simp only [inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  rw [real_inner_comm]
  ring

private theorem defectSource_wick_diagonal_pairing {n : ℕ} {P : Type*}
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] (B : Fin n → Fin n → P) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      if i = j ∧ k = l then inner ℝ (B i j) (B k l) else 0) = ‖∑ i, B i i‖ ^ 2 := by
  calc
    _ = ∑ i, ∑ k, inner ℝ (B i i) (B k k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single i]
      · simp [Finset.sum_ite_eq, Finset.mem_univ]
      · intro j hj hji
        simp [Ne.symm hji]
      · simp
    _ = _ := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sum, sum_inner]
      conv_rhs => rw [Finset.sum_comm]

private theorem defectSource_wick_first_crossing {n : ℕ} {P : Type*}
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] (B : Fin n → Fin n → P) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      if i = k ∧ j = l then inner ℝ (B i j) (B k l) else 0) =
      ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
  calc
    _ = ∑ i, ∑ j, inner ℝ (B i j) (B i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_eq_single i]
      · simp [Finset.sum_ite_eq, Finset.mem_univ]
      · intro k hk hki
        simp [Ne.symm hki]
      · simp
    _ = _ := by simp

private theorem defectSource_wick_second_crossing {n : ℕ} {P : Type*}
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] (B : Fin n → Fin n → P) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      if i = l ∧ j = k then inner ℝ (B i j) (B k l) else 0) =
      ∑ i, ∑ j, inner ℝ (B i j) (B j i) := by
  calc
    _ = ∑ i, ∑ j, inner ℝ (B i j) (B j i) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_eq_single j]
      · simp [Finset.sum_ite_eq, Finset.mem_univ]
      · intro k hk hkj
        simp [Ne.symm hkj]
      · simp

/-- Wick's three pairings are the exact second moment of the actual Hilbert defect source. -/
theorem defectSource_gaussian_energy_formula {n : ℕ} {P : Type*}
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] (B : Fin n → Fin n → P) :
    (∫ x, ‖defectSource B x‖ ^ 2 ∂standardGaussianPi n) =
      ‖∑ i, B i i‖ ^ 2 +
        ∑ i, ∑ j, ‖B i j‖ ^ 2 +
        ∑ i, ∑ j, inner ℝ (B i j) (B j i) := by
  have hpoint := defectSource_norm_sq_expansion B
  have hTerm (i j k l : Fin n) :
      Integrable (fun x : Fin n → ℝ => inner ℝ (B i j) (B k l) *
        (x i * x j * (x k * x l))) (standardGaussianPi n) := by
    have h := (integrable_gaussian_monomial [i,j,k,l]).const_mul
      (inner ℝ (B i j) (B k l))
    have he : (fun x : Fin n → ℝ => inner ℝ (B i j) (B k l) *
        (x i * x j * (x k * x l))) =
        fun x => inner ℝ (B i j) (B k l) * gaussianMonomial [i,j,k,l] x := by
      funext x
      congr 1
      simp [gaussianMonomial]
      ring
    rw [he]
    exact h
  have hSumL (i j k : Fin n) :
      Integrable (fun x : Fin n → ℝ => ∑ l, inner ℝ (B i j) (B k l) *
        (x i * x j * (x k * x l))) (standardGaussianPi n) :=
    integrable_finsetSum _ (fun l _ => hTerm i j k l)
  have hSumK (i j : Fin n) :
      Integrable (fun x : Fin n → ℝ => ∑ k, ∑ l, inner ℝ (B i j) (B k l) *
        (x i * x j * (x k * x l))) (standardGaussianPi n) :=
    integrable_finsetSum _ (fun k _ => hSumL i j k)
  have hSumJ (i : Fin n) :
      Integrable (fun x : Fin n → ℝ => ∑ j, ∑ k, ∑ l, inner ℝ (B i j) (B k l) *
        (x i * x j * (x k * x l))) (standardGaussianPi n) :=
    integrable_finsetSum _ (fun j _ => hSumK i j)
  rw [show (fun x : Fin n → ℝ => ‖defectSource B x‖ ^ 2) =
      fun x => ∑ i, ∑ j, ∑ k, ∑ l,
        inner ℝ (B i j) (B k l) * (x i * x j * (x k * x l)) by
      funext x
      exact hpoint x]
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ l,
        ∫ x, inner ℝ (B i j) (B k l) * (x i * x j * (x k * x l))
          ∂standardGaussianPi n := by
      rw [integral_finsetSum _ (fun i _ => hSumJ i)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ (fun j _ => hSumK i j)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_finsetSum _ (fun k _ => hSumL i j k)]
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_finsetSum _ (fun l _ => hTerm i j k l)]
    _ = ∑ i, ∑ j, ∑ k, ∑ l,
        inner ℝ (B i j) (B k l) *
          ((if i = j ∧ k = l then 1 else 0) +
            (if i = k ∧ j = l then 1 else 0) +
            (if i = l ∧ j = k then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      rw [integral_const_mul, standardGaussian_fourth_coordinate_moment]
    _ = ‖∑ i, B i i‖ ^ 2 + ∑ i, ∑ j, ‖B i j‖ ^ 2 +
        ∑ i, ∑ j, inner ℝ (B i j) (B j i) := by
      simp_rw [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, mul_one]
      rw [defectSource_wick_diagonal_pairing, defectSource_wick_first_crossing,
        defectSource_wick_second_crossing]

private theorem defectSource_cross_sum_le {n : ℕ} {P : Type*}
    [NormedAddCommGroup P] [InnerProductSpace ℝ P] (B : Fin n → Fin n → P) :
    (∑ i, ∑ j, inner ℝ (B i j) (B j i)) ≤ ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
  calc
    _ ≤ ∑ i, ∑ j, ‖B i j‖ * ‖B j i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact real_inner_le_norm _ _
    _ ≤ ∑ i, ∑ j, (‖B i j‖ ^ 2 + ‖B j i‖ ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      nlinarith [sq_nonneg (‖B i j‖ - ‖B j i‖)]
    _ = ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
      calc
        _ = (∑ i, ∑ j, (‖B i j‖ ^ 2 + ‖B j i‖ ^ 2)) / 2 := by
          simp only [← Finset.sum_div]
        _ = (∑ i, ∑ j, ‖B i j‖ ^ 2 + ∑ i, ∑ j, ‖B j i‖ ^ 2) / 2 := by
          congr 1
          simp only [Finset.sum_add_distrib]
        _ = _ := by
          rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
            (f := fun i j : Fin n => ‖B j i‖ ^ 2)]
          ring

/-- Defect energy from the row and column covariance bounds of the projected source. -/
theorem projected_source_defect_energy_bound {n : ℕ} {W P : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    (T : Fin n → W →L[ℝ] P) (d : Fin n → W) (κ : ℝ)
    (hcol : ∀ u : W, ∑ i, ‖T i u‖ ^ 2 ≤ κ ^ 2 * ‖u‖ ^ 2)
    (hrow : ∀ u : Fin n → W,
      ‖∑ i, T i (u i)‖ ^ 2 ≤ κ ^ 2 * ∑ i, ‖u i‖ ^ 2) :
    (∫ x, ‖defectSource (fun i j => T i (d j)) x‖ ^ 2 ∂standardGaussianPi n) ≤
      3 * κ ^ 2 * ∑ j, ‖d j‖ ^ 2 := by
  let B : Fin n → Fin n → P := fun i j => T i (d j)
  rw [defectSource_gaussian_energy_formula B]
  have hm : ‖∑ i, B i i‖ ^ 2 ≤ κ ^ 2 * ∑ i, ‖d i‖ ^ 2 := by
    simpa only [B] using hrow d
  have hc : ∑ i, ∑ j, ‖B i j‖ ^ 2 ≤ κ ^ 2 * ∑ j, ‖d j‖ ^ 2 := by
    rw [Finset.sum_comm]
    calc
      ∑ j, ∑ i, ‖B i j‖ ^ 2 ≤ ∑ j, κ ^ 2 * ‖d j‖ ^ 2 :=
        Finset.sum_le_sum (fun j hj => by simpa only [B] using hcol (d j))
      _ = κ ^ 2 * ∑ j, ‖d j‖ ^ 2 := by rw [Finset.mul_sum]
  have hx := defectSource_cross_sum_le B
  calc
    _ ≤ κ ^ 2 * ∑ i, ‖d i‖ ^ 2 +
        ∑ i, ∑ j, ‖B i j‖ ^ 2 + ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
      have hcross := defectSource_cross_sum_le B
      exact add_le_add (add_le_add hm le_rfl) hcross
    _ ≤ 3 * κ ^ 2 * ∑ j, ‖d j‖ ^ 2 := by
      have hfirst : ‖∑ i, B i i‖ ^ 2 ≤ κ ^ 2 * ∑ j, ‖d j‖ ^ 2 := by simpa using hm
      have hsecond : ∑ i, ∑ j, ‖B i j‖ ^ 2 ≤ κ ^ 2 * ∑ j, ‖d j‖ ^ 2 := hc
      linarith

end ASDExplicitGamma.Scalar
