module

public import ASDExplicitGamma.Cold.ColdRoundingAlgebra

/-! # Finite real sums under outward rounding -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- Real lower bounds for terms survive the outward-addition fold. -/
theorem cold_le_up_sum_fold (xs : List ℕ) (f : ℕ → ℝ) (F : ℕ → ℚ)
    {a : ℝ} {A : ℚ} (ha : a ≤ (A:ℝ)) (hf : ∀ k ∈ xs, f k ≤ (F k:ℝ)) :
    a+(xs.map f).sum ≤ (xs.foldl (fun acc k => coldUpAdd acc (F k)) A:ℚ) := by
  induction xs generalizing a A with
  | nil => simpa only [List.map_nil,List.sum_nil,List.foldl_nil,add_zero] using ha
  | cons k xs ih =>
    simp only [List.map_cons,List.sum_cons,List.foldl_cons]
    rw [← add_assoc]
    exact ih (cold_up_add_mono ha (hf k (by simp))) (fun i hi => hf i (by simp [hi]))

/-- The source finite sum is the real list sum used by the exact recurrence. -/
theorem cold_range_list_sum (f : ℕ → ℝ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ r ∈ Finset.range n, f r := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.range_succ,List.map_append,List.map_singleton,List.sum_append,
      List.sum_singleton,Finset.sum_range_succ,ih]

/-- Exact rational finite sums are ordinary finite real sums after casting. -/
theorem cold_list_sum_range_cast (f : ℕ → ℚ) (n : ℕ) :
    (coldListSum (List.range n) f:ℝ) = ∑ r ∈ Finset.range n, (f r:ℝ) := by
  rw [← coldRealListSum_cast]
  exact cold_range_list_sum _ _

end ASDExplicitGamma.Cold
