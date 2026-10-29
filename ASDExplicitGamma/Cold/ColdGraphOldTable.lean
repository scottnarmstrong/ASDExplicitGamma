module

public import ASDExplicitGamma.Cold.ColdGraphBranchTable

/-! # Soundness of the old global/decay graph branch -/

@[expose] public section
noncomputable section
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- The exact native interpolation radical fits the stored outward root. -/
theorem cold_native_variance_radical_table :
    Real.sqrt (2*(coldA:ℝ)+(coldL0:ℝ)^2) ≤ (coldV0Upper:ℝ) := by
  have hround := cold_round_up_real (2*coldA+coldL0^2)
  have hs : (coldRoundUp (2*coldA+coldL0^2):ℝ) ≤ (coldV0Upper:ℝ)^2 := by
    exact_mod_cast cold_v0_endpoint_check.1
  have hp : 2*(coldA:ℝ)+(coldL0:ℝ)^2 ≤ (coldV0Upper:ℝ)^2 := by
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow] using hround.trans hs
  apply (Real.sqrt_le_iff).mpr
  exact ⟨by norm_num [coldV0Upper],hp⟩

/-- Both exact old graph branches are bounded by the rational producing expression. -/
theorem cold_old_graph_table (ell : ℕ) :
    coldOldGraphCap (coldA:ℝ) (coldL0:ℝ) ell ≤ (coldOldGraph ell:ℝ) := by
  unfold coldOldGraphCap coldOldGraph
  rw [Rat.cast_min]
  apply min_le_min
  · have hnorm : 2*(coldA:ℝ)+2*(Real.sqrt (2*(coldA:ℝ)+(coldL0:ℝ)^2)+(coldL0:ℝ))*
        (3:ℝ)^(-(ell:ℝ)) ≤
      2*(coldA:ℝ)+2*((coldV0Upper:ℝ)+(coldL0:ℝ))*(3:ℝ)^(-(ell:ℝ)) := by
      have h := mul_le_mul_of_nonneg_right
        (add_le_add_right cold_native_variance_radical_table (coldL0:ℝ))
        (show 0 ≤ 2*(3:ℝ)^(-(ell:ℝ)) by positivity)
      linarith only [h]
    have hn : 0 ≤ 2*(coldA:ℝ)+2*(Real.sqrt (2*(coldA:ℝ)+(coldL0:ℝ)^2)+(coldL0:ℝ))*
        (3:ℝ)^(-(ell:ℝ)) := by
      have ha : 0 ≤ (coldA:ℝ) := by norm_num [coldA]
      have hL : 0 ≤ (coldL0:ℝ) := by norm_num [coldL0]
      positivity
    have hp := (sq_le_sq₀ hn (hn.trans hnorm)).mpr hnorm
    push_cast
    rw [cold_table_decay]
    linarith only [hp]
  · push_cast
    exact le_rfl

end ASDExplicitGamma.Cold
