module

public import ASDExplicitGamma.Cold.ColdTableConstants
public import ASDExplicitGamma.Cold.HistoryParameters
public import ASDExplicitGamma.Numerics.Cold.History

/-! # Soundness of the outward alpha/beta power tables -/

@[expose] public section
noncomputable section
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- Downward rounding never exceeds its rational input. -/
theorem cold_round_down_le (x : ℚ) : coldRoundDown x ≤ x := by
  have hs : 0 < coldScaleQ := by norm_num [coldScaleQ,coldScale]
  apply (div_le_iff₀ hs).mpr
  simpa only [coldRoundDown,coldScaleQ,mul_comm] using Int.floor_le ((coldScaleQ:ℚ)*x)

/-- All entries needed by the finite replay have nonnegative signs. -/
theorem cold_power_table_nonneg : ∀ n ∈ List.range 129,
    0 ≤ coldAlphaPowLower n ∧ 0 ≤ coldAlphaPowUpper n ∧ 0 ≤ coldBetaPowUpper n := by
  decide +kernel

/-- Lower and upper tabulated alpha powers enclose the exact source weight. -/
theorem cold_alpha_power_table (n : ℕ) (hn : n ≤ 128) :
    (coldAlphaPowLower n:ℝ) ≤ coldHistoryAlpha^n ∧
      coldHistoryAlpha^n ≤ (coldAlphaPowUpper n:ℝ) := by
  induction n with
  | zero => simp only [cold_power_tables_check.1,cold_power_tables_check.2.1,pow_zero,Rat.cast_one,le_refl,and_self]
  | succ n ih =>
    have hn128 : n ≤ 128 := by omega
    have hnmem : n ∈ List.range 128 := List.mem_range.mpr (by omega)
    have hi := ih hn128
    have hc := cold_power_tables_check.2.2.2 n hnmem
    have hsign := cold_power_table_nonneg n (List.mem_range.mpr (by omega))
    constructor
    · rw [hc.2.1]
      have hr : (coldRoundDown (coldAlphaPowLower n*coldAlphaLower):ℝ) ≤
          (coldAlphaPowLower n:ℝ)*(coldAlphaLower:ℝ) := by exact_mod_cast cold_round_down_le (coldAlphaPowLower n*coldAlphaLower)
      have hm := mul_le_mul hi.1 coldAlpha_interval_sound.1
        (by exact_mod_cast (show 0 ≤ coldAlphaLower by norm_num [coldAlphaLower]))
        (pow_nonneg coldHistoryAlpha_pos.le _)
      rw [pow_succ]
      exact hr.trans hm
    · rw [hc.1]
      have hr : (coldAlphaPowUpper n:ℝ)*(coldAlphaUpper:ℝ) ≤
          (coldRoundUp (coldAlphaPowUpper n*coldAlphaUpper):ℝ) := by exact_mod_cast coldRoundUp_ge (coldAlphaPowUpper n*coldAlphaUpper)
      have hm := mul_le_mul hi.2 coldAlpha_interval_sound.2 coldHistoryAlpha_pos.le
        (Rat.cast_nonneg.mpr hsign.2.1)
      rw [pow_succ]
      exact hm.trans hr

/-- Tabulated beta powers dominate the exact complete-tail weight. -/
theorem cold_beta_power_table (n : ℕ) (hn : n ≤ 128) :
    coldHistoryBeta^n ≤ (coldBetaPowUpper n:ℝ) := by
  induction n with
  | zero => simp only [cold_power_tables_check.2.2.1,pow_zero,Rat.cast_one,le_refl]
  | succ n ih =>
    have hn128 : n ≤ 128 := by omega
    have hnmem : n ∈ List.range 128 := List.mem_range.mpr (by omega)
    have hc := (cold_power_tables_check.2.2.2 n hnmem).2.2
    rw [hc]
    have hr : (coldBetaPowUpper n:ℝ)*(coldBetaUpper:ℝ) ≤
        (coldRoundUp (coldBetaPowUpper n*coldBetaUpper):ℝ) := by exact_mod_cast coldRoundUp_ge (coldBetaPowUpper n*coldBetaUpper)
    have hsign := cold_power_table_nonneg n (List.mem_range.mpr (by omega))
    have hm := mul_le_mul (ih hn128) coldBeta_interval_sound.2 coldHistoryBeta_pos.le
      (Rat.cast_nonneg.mpr hsign.2.2)
    rw [pow_succ]
    exact hm.trans hr

end ASDExplicitGamma.Cold
