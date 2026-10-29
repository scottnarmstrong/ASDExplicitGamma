module

public import ASDExplicitGamma.Cold.ColdTableConstants

/-! # Soundness of the checked moment table, including proportional input caps -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- The entire checked moment table bounds actual same-law source traces.
Only strictly earlier ordinary-mean caps are consumed at each lag. The arbitrary
nonnegative scaling factor is retained for the final proportional continuation. -/
theorem cold_moment_table_caps {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] (F : ColdMomentSystem Ω ℙ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hroot : lpNorm (F.trace 0) 20 ℙ ≤ θ*(coldR20:ℝ)) {n : ℕ} (hn : n ≤ 128)
    (hmean : ∀ k < n, (∫ ω, F.trace k ω ∂ℙ) ≤ θ*(coldMeanAt k:ℝ)) :
    lpNorm (F.trace n) 20 ℙ ≤ θ*(coldMomentAt n:ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hnmem : n ∈ List.range 129 := List.mem_range.mpr (by omega)
    rw [cold_moment_table_check n hnmem]
    by_cases hn0 : n = 0
    · subst n
      simpa [coldMomentExpected] using hroot
    · rw [coldMomentExpected,ite_eq_right hn0]
      have hr : 0 ≤ θ*(coldR20:ℝ) := by
        exact lpNorm_nonneg.trans hroot
      have hinit : lpNorm (F.trace n) 20 ℙ ≤ θ*(coldInitialMoment n:ℝ) := by
        have hu := F.update (Nat.pos_of_ne_zero hn0) hr hroot
          (by simpa only [cold_table_zero.1] using hmean 0 (Nat.pos_of_ne_zero hn0))
        have hc := cold_centered_cap_le_table (M := coldR20) hθ (by norm_num [coldR20]) (Nat.pos_of_ne_zero hn0)
        rw [Nat.sub_zero] at hu
        rw [coldInitialMoment,ite_eq_right hn0,Rat.cast_min,Rat.cast_add,Rat.cast_mul,
          Rat.cast_mul,cold_table_decay,mul_min_of_nonneg _ _ hθ]
        apply hu.trans
        apply min_le_min le_rfl
        have he := min_le_right (coldR20:ℝ)
          ((coldSqrt19Upper:ℝ)*(3:ℝ)^(-(n:ℝ))*(coldR20:ℝ))
        simp only [Rat.cast_min,Rat.cast_mul,cold_table_decay] at hc
        have hc' := hc.trans (mul_le_mul_of_nonneg_left he hθ)
        nlinarith only [hc']
      have hcand (k : ℕ) (hk : k ∈ List.range n) :
          lpNorm (F.trace n) 20 ℙ ≤ θ*(coldMomentCandidate n k:ℝ) := by
        have hklt : k < n := List.mem_range.mp hk
        have hk128 : k ≤ 128 := by omega
        have hm := ih k hklt hk128 (fun i hi => hmean i (hi.trans hklt))
        have hM := cold_table_nonneg k (List.mem_range.mpr (by omega))
        have hc := cold_centered_cap_le_table hθ hM.2 (Nat.sub_pos_of_lt hklt)
        have hu := F.update hklt (mul_nonneg hθ (Rat.cast_nonneg.mpr hM.2)) hm (hmean k hklt)
        apply hu.trans
        change min (θ*(coldMomentAt k:ℝ))
          (θ*(coldMeanAt k:ℝ)+coldCenteredMomentCap (θ*(coldMomentAt k:ℝ)) (n-k)) ≤ _
        have he : θ*(coldMomentCandidate n k:ℝ) =
            min (θ*(coldMomentAt k:ℝ))
              (θ*(coldMeanAt k:ℝ)+θ*((min (coldMomentAt k)
                (coldSqrt19Upper*coldDecay (n-k)*coldMomentAt k):ℚ):ℝ)) := by
          dsimp only [coldMomentCandidate]
          rw [Rat.cast_min,Rat.cast_add,mul_min_of_nonneg _ _ hθ,mul_add]
        rw [he]
        exact min_le_min le_rfl (add_le_add le_rfl hc)
      have hf := cold_le_scaled_fold_min (List.range n) (coldMomentCandidate n) hθ hinit hcand
      exact hf.trans (mul_le_mul_of_nonneg_left (Rat.cast_le.mpr (coldRoundUp_ge _)) hθ)

end ASDExplicitGamma.Cold
