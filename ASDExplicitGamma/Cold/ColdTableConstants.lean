module

public import ASDExplicitGamma.Numerics.Cold.Bounds
public import ASDExplicitGamma.Numerics.Cold.RealDominance
public import ASDExplicitGamma.Cold.ColdMomentRecursion

/-! # Analytic consumers of the rational cold moment table -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- The certified coefficient is an upper bound for the sharp four-colour constant. -/
theorem cold_table_sqrt19_upper : 2*Real.sqrt 19 ≤ (coldSqrt19Upper:ℝ) := by
  have he := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 19)
  have hq : 0 ≤ (coldSqrt19Upper:ℝ) := by norm_num [coldSqrt19Upper]
  have hsq : (2:ℝ)^2*19 ≤ (coldSqrt19Upper:ℝ)^2 := by norm_num [coldSqrt19Upper]
  nlinarith only [he,hq,hsq,Real.sqrt_nonneg 19]

/-- The rational decay is exactly the analytic triadic decay. -/
theorem cold_table_decay (d : ℕ) : (coldDecay d:ℝ) = (3:ℝ)^(-(d:ℝ)) := by
  norm_num [coldDecay,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3),Real.rpow_natCast,inv_pow]
  rw [one_div,inv_pow]

/-- The stored means and moments have their required signs. -/
theorem cold_table_nonneg : ∀ k ∈ List.range 129,
    0 ≤ coldMeanAt k ∧ 0 ≤ coldMomentAt k := by
  decide +kernel

/-- The initial stored trace inputs agree with the endpoint constants. -/
theorem cold_table_zero : coldMeanAt 0 = coldA ∧ coldMomentAt 0 = coldR20 := by
  decide +kernel

/-- Every rational centered cap dominates its exact scaled analytic counterpart. -/
theorem cold_centered_cap_le_table {θ : ℝ} (hθ : 0 ≤ θ) {M : ℚ} (hM : 0 ≤ M)
    {d : ℕ} (hd : 0 < d) :
    coldCenteredMomentCap (θ*(M:ℝ)) d ≤
      θ*((min M (coldSqrt19Upper*coldDecay d*M):ℚ):ℝ) := by
  rw [coldCenteredMomentCap,ite_eq_right (Nat.ne_of_gt hd),Rat.cast_min,Rat.cast_mul,
    Rat.cast_mul,cold_table_decay,mul_min_of_nonneg _ _ hθ]
  apply min_le_min le_rfl
  have hc := mul_le_mul_of_nonneg_right cold_table_sqrt19_upper
    (show 0 ≤ (3:ℝ)^(-(d:ℝ))*(θ*(M:ℝ)) by positivity)
  nlinarith only [hc]

/-- Any lower bound for all entries remains a lower bound for a finite minimum fold. -/
theorem cold_le_fold_min (xs : List ℕ) (f : ℕ → ℚ) {x : ℝ} {a : ℚ}
    (ha : x ≤ (a:ℝ)) (hf : ∀ k ∈ xs, x ≤ (f k:ℝ)) :
    x ≤ (xs.foldl (fun acc k => min acc (f k)) a:ℚ) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons k xs ih =>
    apply ih
    · simpa only [Rat.cast_min] using le_min ha (hf k (by simp))
    · intro i hi
      exact hf i (by simp [hi])

/-- Scaling by a nonnegative factor commutes with a finite minimum fold. -/
theorem cold_le_scaled_fold_min (xs : List ℕ) (f : ℕ → ℚ) {x θ : ℝ} {a : ℚ}
    (hθ : 0 ≤ θ) (ha : x ≤ θ*(a:ℝ)) (hf : ∀ k ∈ xs, x ≤ θ*(f k:ℝ)) :
    x ≤ θ*(xs.foldl (fun acc k => min acc (f k)) a:ℚ) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons k xs ih =>
    apply ih
    · simpa only [Rat.cast_min,mul_min_of_nonneg _ _ hθ] using le_min ha (hf k (by simp))
    · intro i hi
      exact hf i (by simp [hi])

end ASDExplicitGamma.Cold
