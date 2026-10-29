module

public import ASDExplicitGamma.Cold.PlateauFiniteSchur
public import ASDExplicitGamma.Cold.PlateauTransportAlgebra

/-! # Finite transport assembly before taking any martingale limit -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The two finite top/fine rows have the sharp combined geometric charge. -/
theorem plateau_finite_cross_le (S : Finset ℕ) (hS : ∀ k ∈ S, 1 ≤ k)
    (a b : ℕ → ℝ) (ha : ∀ k ∈ S, 0 ≤ a k) (hb : ∀ k ∈ S, 0 ≤ b k)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * (∑ k ∈ S, (1 / 9 : ℝ) ^ k * b k) +
      y * (∑ k ∈ S, (1 / 9 : ℝ) ^ k * a k) ≤
      Real.sqrt ((x ^ 2 + y ^ 2) *
        ((∑ k ∈ S, (1 / 9 : ℝ) ^ k * a k ^ 2) +
         (∑ k ∈ S, (1 / 9 : ℝ) ^ k * b k ^ 2))) / Real.sqrt 8 := by
  let A := ∑ k ∈ S, (1 / 9 : ℝ) ^ k * a k
  let B := ∑ k ∈ S, (1 / 9 : ℝ) ^ k * b k
  let R := (∑ k ∈ S, (1 / 9 : ℝ) ^ k * a k ^ 2) +
    (∑ k ∈ S, (1 / 9 : ℝ) ^ k * b k ^ 2)
  have hA : 0 ≤ A := Finset.sum_nonneg fun k hk => mul_nonneg (by positivity) (ha k hk)
  have hB : 0 ≤ B := Finset.sum_nonneg fun k hk => mul_nonneg (by positivity) (hb k hk)
  have hR : 0 ≤ R := add_nonneg
    (Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (sq_nonneg _))
    (Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (sq_nonneg _))
  have hAB : A ^ 2 + B ^ 2 ≤ R / 8 := by
    have h1 := plateau_finite_top_fine_sq S hS a
    have h2 := plateau_finite_top_fine_sq S hS b
    change A ^ 2 ≤ _ at h1
    change B ^ 2 ≤ _ at h2
    dsimp [R]
    linarith only [h1, h2]
  have hcs : (x * B + y * A) ^ 2 ≤ (x ^ 2 + y ^ 2) * (A ^ 2 + B ^ 2) := by
    nlinarith only [sq_nonneg (x * A - y * B)]
  have hm := mul_le_mul_of_nonneg_left hAB (add_nonneg (sq_nonneg x) (sq_nonneg y))
  have hs : 0 < Real.sqrt (8 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  apply (le_div_iff₀ hs).mpr
  apply (sq_le_sq₀ (mul_nonneg (add_nonneg (mul_nonneg hx hB) (mul_nonneg hy hA)) hs.le)
    (Real.sqrt_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8),
    Real.sq_sqrt (mul_nonneg (add_nonneg (sq_nonneg x) (sq_nonneg y)) hR)]
  nlinarith only [hcs, hm]

/-- The complete finite numerical transport assembly from its genuine entry estimates. -/
theorem plateau_finite_entry_assembly (S : Finset ℕ) (hS : ∀ k ∈ S, 1 ≤ k)
    (a b : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k)
    (t : ℕ → ℕ → ℝ)
    (h00 : |t 0 0| ≤ a 0 ^ 2 + b 0 ^ 2)
    (h0 : ∀ l ∈ S, |t 0 l| ≤ (48 / (7 * Real.pi)) * (1 / 9 : ℝ) ^ l * a 0 * b l)
    (h1 : ∀ k ∈ S, |t k 0| ≤ (48 / (7 * Real.pi)) * (1 / 9 : ℝ) ^ k * a k * b 0)
    (hf : ∀ k ∈ S, ∀ l ∈ S, |t k l| ≤
      (48 / (7 * Real.pi)) * (1 / 9 : ℝ) ^ max k l * a k * b l) :
    2 * |t 0 0 + (∑ l ∈ S, t 0 l) + (∑ k ∈ S, t k 0) +
        ∑ k ∈ S, ∑ l ∈ S, t k l| ≤
      (9 / 4 : ℝ) * (a 0 ^ 2 + b 0 ^ 2) + 7 *
        ((∑ k ∈ S, (1 / 9 : ℝ) ^ k * a k ^ 2) +
         (∑ k ∈ S, (1 / 9 : ℝ) ^ k * b k ^ 2)) := by
  let C := (48 : ℝ) / (7 * Real.pi)
  let R := (∑ k ∈ S, (1 / 9 : ℝ) ^ k * a k ^ 2) +
    (∑ k ∈ S, (1 / 9 : ℝ) ^ k * b k ^ 2)
  let V := a 0 ^ 2 + b 0 ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hR : 0 ≤ R := add_nonneg
    (Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (sq_nonneg _))
    (Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (sq_nonneg _))
  have hrow0 : |∑ l ∈ S, t 0 l| ≤ C * a 0 * (∑ l ∈ S, (1 / 9 : ℝ) ^ l * b l) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    convert h0 l hl using 1
    ring
  have hrow1 : |∑ k ∈ S, t k 0| ≤ C * b 0 * (∑ k ∈ S, (1 / 9 : ℝ) ^ k * a k) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    convert h1 k hk using 1
    ring
  have hfine : |∑ k ∈ S, ∑ l ∈ S, t k l| ≤ C * R := by
    calc
      _ ≤ ∑ k ∈ S, ∑ l ∈ S, |t k l| := (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ k ∈ S, ∑ l ∈ S, C * (1 / 9 : ℝ) ^ max k l * a k * b l :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl => hf k hk l hl
      _ = C * (∑ k ∈ S, ∑ l ∈ S, (1 / 9 : ℝ) ^ max k l * a k * b l) := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ ≤ C * R := mul_le_mul_of_nonneg_left (plateau_finite_fine_sum S S a b) hC
  have hcross := mul_le_mul_of_nonneg_left
    (plateau_finite_cross_le S hS a b (fun k _ => ha k) (fun k _ => hb k)
      (a 0) (b 0) (ha 0) (hb 0)) hC
  have htri1 := abs_add_le (t 0 0) (∑ l ∈ S, t 0 l)
  have htri2 := abs_add_le (t 0 0 + ∑ l ∈ S, t 0 l) (∑ k ∈ S, t k 0)
  have htri3 := abs_add_le (t 0 0 + (∑ l ∈ S, t 0 l) + ∑ k ∈ S, t k 0)
    (∑ k ∈ S, ∑ l ∈ S, t k l)
  apply plateau_transport_assembly (add_nonneg (sq_nonneg _) (sq_nonneg _)) hR
  have heq : C * (Real.sqrt (V * R) / Real.sqrt 8) =
      (48 / (7 * Real.pi * Real.sqrt 8)) * Real.sqrt (V * R) := by dsimp [C]; ring
  change C * _ ≤ C * (Real.sqrt (V * R) / Real.sqrt 8) at hcross
  rw [heq] at hcross
  change _ ≤ V + (48 / (7 * Real.pi * Real.sqrt 8)) * Real.sqrt (V * R) + C * R
  dsimp [V] at *
  linarith only [h00, hrow0, hrow1, hfine, hcross, htri1, htri2, htri3]

end ASDExplicitGamma.Cold
