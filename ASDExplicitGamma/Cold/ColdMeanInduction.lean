module

public import ASDExplicitGamma.Cold.ColdMeanStep

/-! # Strictly triangular induction for the checked mean table -/

@[expose] public section
noncomputable section
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- The odd entries of the stored mean table copy the preceding even lag. -/
theorem cold_mean_table_odd_copy : ∀ j ∈ List.range 129, ¬Even j →
    coldMeanAt j = coldMeanAt (j-1) := by
  decide +kernel

/-- Scalar induction consumer for the actual same-law recurrence. Its recurrence
premise must be produced from the actual plateau/moment/history/graph estimates;
this helper alone does not claim CO-TRIANGULAR-129. -/
theorem cold_mean_table_induction {μ : ℕ → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hmono : Antitone μ) (hroot : μ 0 ≤ θ*(coldA:ℝ))
    (hrec : ∀ j ∈ coldUpdatedLags,
      (∀ k < j, μ k ≤ θ*(coldMeanAt k:ℝ)) →
      coldExactDenominator j*μ j ≤ coldExactWeightedMeans μ j+
        θ*((coldGraphContribution j:ℝ)+(coldBadHistory j:ℝ))) :
    ∀ j ≤ 128, μ j ≤ θ*(coldMeanAt j:ℝ) := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj128
    by_cases hj4 : j < 4
    · rw [cold_initial_mean_values j (List.mem_range.mpr hj4)]
      exact (hmono (Nat.zero_le _)).trans hroot
    · by_cases heven : Even j
      · have hjmem := cold_even_mem_updated j heven (by omega) hj128
        have hprior : ∀ k < j, μ k ≤ θ*(coldMeanAt k:ℝ) := fun k hk => ih k hk (by omega)
        apply cold_mean_step_of_scaled_exact hθ hjmem
          (hmono (Nat.sub_le _ _)) (hrec j hjmem hprior)
          (hprior (j-2) (by omega))
        · intro r hr
          exact hprior (j-r) (cold_transport_index_lt j r hjmem hr)
        · intro r hr
          rcases List.mem_map.mp hr with ⟨i,hi,rfl⟩
          exact hmono (by omega)
      · have hjpos : 0 < j := by omega
        rw [cold_mean_table_odd_copy j (List.mem_range.mpr (by omega)) heven]
        exact (hmono (Nat.sub_le _ _)).trans (ih (j-1) (by omega) (by omega))

end ASDExplicitGamma.Cold
