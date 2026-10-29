module

public import ASDExplicitGamma.Cold.ColdPowerTable

/-! # Outward rational arithmetic consumed by the analytic cold estimates -/

@[expose] public section
noncomputable section
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- The rational outward product dominates its exact real value. -/
theorem cold_up_mul_ge (x y : ℚ) : (x:ℝ)*(y:ℝ) ≤ (coldUpMul x y:ℝ) := by
  exact_mod_cast coldRoundUp_ge (x*y)

/-- The rational outward sum dominates its exact real value. -/
theorem cold_up_add_ge (x y : ℚ) : (x:ℝ)+(y:ℝ) ≤ (coldUpAdd x y:ℝ) := by
  exact_mod_cast coldRoundUp_ge (x+y)

/-- Nonnegative input comparisons may be multiplied and rounded outward. -/
theorem cold_up_mul_mono {x y : ℝ} {X Y : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hX : x ≤ (X:ℝ)) (hY : y ≤ (Y:ℝ)) : x*y ≤ (coldUpMul X Y:ℝ) :=
  (mul_le_mul hX hY hy (hx.trans hX)).trans (cold_up_mul_ge X Y)

/-- Input comparisons may be added and rounded outward. -/
theorem cold_up_add_mono {x y : ℝ} {X Y : ℚ}
    (hX : x ≤ (X:ℝ)) (hY : y ≤ (Y:ℝ)) : x+y ≤ (coldUpAdd X Y:ℝ) :=
  (add_le_add hX hY).trans (cold_up_add_ge X Y)

/-- The table's rounded scalar is an upper bound in the actual real field. -/
theorem cold_round_up_real (x : ℚ) : (x:ℝ) ≤ (coldRoundUp x:ℝ) := by
  exact_mod_cast coldRoundUp_ge x

/-- The history's d=0 centered cap is also dominated by its rational definition. -/
theorem cold_centered_cap_le_history (k d : ℕ) (hk : k ≤ 128) :
    coldCenteredMomentCap (coldMomentAt k:ℝ) d ≤ (coldHistoryE k d:ℝ) := by
  have hM := (cold_table_nonneg k (List.mem_range.mpr (by omega))).2
  by_cases hd : d = 0
  · subst d
    have hC : (1:ℚ) ≤ coldSqrt19Upper := by norm_num [coldSqrt19Upper]
    have hmul : coldMomentAt k ≤ coldSqrt19Upper*coldMomentAt k := by
      calc
        coldMomentAt k = 1*coldMomentAt k := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hC hM
    have he : min (coldMomentAt k) (coldSqrt19Upper*coldMomentAt k) = coldMomentAt k :=
      min_eq_left hmul
    simp only [coldCenteredMomentCap,ite_true,coldHistoryE,coldDecay,pow_zero,mul_one,he,le_refl]
  · have h := cold_centered_cap_le_table (M := coldMomentAt k) (θ := 1) (by norm_num) hM
      (Nat.pos_of_ne_zero hd)
    simpa only [one_mul,coldHistoryE] using h

end ASDExplicitGamma.Cold
