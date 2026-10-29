module

public import ASDExplicitGamma.Cold.PlateauSchur
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.NatAbs

/-! # Finite ratio-nine estimates used before the transport limit -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The source ratio-nine decay factors into the symmetric Schur kernel. -/
theorem plateau_decay_factorization (k l : ℕ) :
    (1 / 9 : ℝ) ^ max k l =
      plateauSchurKernel k l * (1 / 3 : ℝ) ^ k * (1 / 3 : ℝ) ^ l := by
  unfold plateauSchurKernel
  have he : k + l + ((k : ℤ) - l).natAbs = 2 * max k l := by
    by_cases h : l ≤ k
    · rw [max_eq_left h, Int.natAbs_natCast_sub_natCast_of_ge h]
      omega
    · rw [max_eq_right (by omega), Int.natAbs_natCast_sub_natCast_of_le (by omega)]
      omega
  have hq : (1 / 9 : ℝ) = (1 / 3) ^ 2 := by norm_num
  rw [hq, ← pow_mul]
  rw [show (1 / 3 : ℝ) ^ ((k : ℤ) - l).natAbs * (1 / 3 : ℝ) ^ k * (1 / 3 : ℝ) ^ l =
      (1 / 3 : ℝ) ^ (k + l + ((k : ℤ) - l).natAbs) by rw [pow_add, pow_add]; ring,
    he, pow_mul]

/-- The finite fine/fine sum is charged to its two weighted square sums. -/
theorem plateau_finite_fine_sum (S T : Finset ℕ) (a b : ℕ → ℝ) :
    (∑ k ∈ S, ∑ l ∈ T, (1 / 9 : ℝ) ^ max k l * a k * b l) ≤
      (∑ k ∈ S, (1 / 9 : ℝ) ^ k * a k ^ 2) +
      (∑ l ∈ T, (1 / 9 : ℝ) ^ l * b l ^ 2) := by
  have h := plateauSchur_finite S T (fun k => (1 / 3 : ℝ) ^ k * a k)
    (fun l => (1 / 3 : ℝ) ^ l * b l)
  have hs (k : ℕ) : ((1 / 3 : ℝ) ^ k) ^ 2 = (1 / 9 : ℝ) ^ k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  simp only [mul_pow, hs] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [plateau_decay_factorization]
  ring

/-- Every finite positive-scale geometric sum is at most the exact tail `1/8`. -/
theorem plateau_finite_geometric_le (S : Finset ℕ) (hS : ∀ k ∈ S, 1 ≤ k) :
    (∑ k ∈ S, (1 / 9 : ℝ) ^ k) ≤ 1 / 8 := by
  have hg := summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 9 : ℝ)‖ < 1)
  have hzero : 0 ∉ S := by intro h; have := hS 0 h; omega
  have h := hg.sum_le_tsum (insert 0 S) (fun _ _ => pow_nonneg (by norm_num) _)
  rw [Finset.sum_insert hzero, pow_zero,
    tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 9 : ℝ)‖ < 1)] at h
  norm_num at h ⊢
  linarith only [h]

/-- Cauchy–Schwarz with the exact positive-scale geometric mass. -/
theorem plateau_finite_top_fine_sq (S : Finset ℕ) (hS : ∀ k ∈ S, 1 ≤ k)
    (a : ℕ → ℝ) :
    (∑ k ∈ S, (1 / 9 : ℝ) ^ k * a k) ^ 2 ≤
      (1 / 8 : ℝ) * (∑ k ∈ S, (1 / 9 : ℝ) ^ k * a k ^ 2) := by
  let q : ℕ → ℝ := fun k => (1 / 3 : ℝ) ^ k
  have hq (k : ℕ) : q k ^ 2 = (1 / 9 : ℝ) ^ k := by
    dsimp [q]
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  have h := Finset.sum_mul_sq_le_sq_mul_sq S q (fun k => q k * a k)
  simp only [mul_pow, hq] at h
  have hsum : (∑ k ∈ S, q k * (q k * a k)) = ∑ k ∈ S, (1 / 9 : ℝ) ^ k * a k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [← mul_assoc, ← sq, hq]
  rw [hsum] at h
  exact h.trans (mul_le_mul_of_nonneg_right (plateau_finite_geometric_le S hS)
    (Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg (by norm_num) _) (sq_nonneg _)))

end ASDExplicitGamma.Cold
