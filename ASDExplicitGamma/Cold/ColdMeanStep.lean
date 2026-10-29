module

public import ASDExplicitGamma.Cold.ColdGraphTable

/-! # The final real-to-rational mean update at a fixed source law -/

@[expose] public section
noncomputable section
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- An actual exact-coefficient plateau inequality and lag subadditivity give the
checked endpoint update. This is a consumer lemma, not an assumption of the recurrence. -/
theorem cold_mean_step_of_exact {μ : ℕ → ℝ} {j : ℕ} (hj : j ∈ coldUpdatedLags)
    (hsub : μ j ≤ μ (j-2))
    (hrec : coldExactDenominator j*μ j ≤ coldExactNumerator μ j)
    (hprev : μ (j-2) ≤ (coldMeanAt (j-2):ℝ))
    (hcap : ∀ r ∈ coldTransportIndices j, μ (j-r) ≤ (coldMeanAt (j-r):ℝ))
    (hmono : ∀ r ∈ coldTransportIndices j, μ (j-2) ≤ μ (j-r)) :
    μ j ≤ (coldMeanAt j:ℝ) := by
  have hden := cold_exact_denominator_pos j hj
  have hratio : μ j ≤ coldExactNumerator μ j/coldExactDenominator j :=
    (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using hrec)
  exact (le_min hsub hratio).trans (cold_exact_step_le_rational μ j hj hprev hcap hmono)

/-- Exact weighted means commute with proportional scaling. -/
theorem coldExactWeightedMeans_scale (μ : ℕ → ℝ) (θ : ℝ) (j : ℕ) :
    coldExactWeightedMeans (fun k => θ*μ k) j = θ*coldExactWeightedMeans μ j := by
  have he (xs : List ℕ) : coldRealListSum xs (fun r => coldExactQ j r*(θ*μ (j-r))) =
      θ*coldRealListSum xs (fun r => coldExactQ j r*μ (j-r)) := by
    induction xs with
    | nil => simp only [coldRealListSum,List.map_nil,List.sum_nil,mul_zero]
    | cons r xs ih =>
      simp only [coldRealListSum,List.map_cons,List.sum_cons] at *
      rw [ih]
      ring
  exact he _

/-- An exact recurrence with proportionally bounded source terms gives the scaled
checked update. The threshold-dependent denominator stays fixed. -/
theorem cold_mean_step_of_scaled_exact {μ : ℕ → ℝ} {θ : ℝ} (hθ : 0 < θ)
    {j : ℕ} (hj : j ∈ coldUpdatedLags)
    (hsub : μ j ≤ μ (j-2))
    (hrec : coldExactDenominator j*μ j ≤ coldExactWeightedMeans μ j+
      θ*((coldGraphContribution j:ℝ)+(coldBadHistory j:ℝ)))
    (hprev : μ (j-2) ≤ θ*(coldMeanAt (j-2):ℝ))
    (hcap : ∀ r ∈ coldTransportIndices j, μ (j-r) ≤ θ*(coldMeanAt (j-r):ℝ))
    (hmono : ∀ r ∈ coldTransportIndices j, μ (j-2) ≤ μ (j-r)) :
    μ j ≤ θ*(coldMeanAt j:ℝ) := by
  let scaledMean := fun k => μ k/θ
  have heq : (fun k => θ*scaledMean k) = μ := by
    funext k
    dsimp only [scaledMean]
    exact mul_div_cancel₀ _ (ne_of_gt hθ)
  have hw := coldExactWeightedMeans_scale scaledMean θ j
  rw [heq] at hw
  have hrec' : coldExactDenominator j*scaledMean j ≤ coldExactNumerator scaledMean j := by
    unfold coldExactNumerator
    rw [hw] at hrec
    apply (mul_le_mul_iff_right₀ hθ).mp
    have hd : θ*(coldExactDenominator j*scaledMean j) = coldExactDenominator j*μ j := by
      dsimp only [scaledMean]
      field_simp
    rw [hd]
    convert hrec using 1
    ring

  have hp : scaledMean j ≤ (coldMeanAt j:ℝ) := cold_mean_step_of_exact hj
    (div_le_div_of_nonneg_right hsub hθ.le) hrec'
    ((div_le_iff₀ hθ).mpr (by simpa only [mul_comm] using hprev))
    (fun r hr => (div_le_iff₀ hθ).mpr (by simpa only [mul_comm] using hcap r hr))
    (fun r hr => div_le_div_of_nonneg_right (hmono r hr) hθ.le)
  exact (div_le_iff₀ hθ).mp hp |>.trans_eq (mul_comm _ _)

end ASDExplicitGamma.Cold
