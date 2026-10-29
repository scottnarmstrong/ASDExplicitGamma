module

public import ASDExplicitGamma.Inverse.FullResponseSelectedRows

/-! Positivity of the retained analytic profiles used in endpoint substitution. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- All selected and retained leading profile factors have their literal
nonnegative meanings before the numerical endpoint substitution. -/
theorem full_response_profile_signs (γ p : ℝ) (hg : γ ≤ gammaZero) (hp : 0 ≤ p) :
    0 ≤ rootLayerSum (2*γ) ∧ 0 ≤ fullResponseWaveLayerMass γ ∧
    0 ≤ fullResponseWaveLayerFirst γ ∧ 0 ≤ selectedJp γ p 377 ∧
    0 ≤ physicalSelectedWaveBudget γ p 377 0 ∧ 0 ≤ physicalSelectedWaveBudget γ p 377 1 := by
  have hA := full_response_wave_layer_profiles γ hg
  have h0 : 0 ≤ rootLayerSum (2*γ) :=
    tsum_nonneg (fun k => mul_nonneg (bankLayerWeight_nonneg k) (by positivity))
  have hmass : 0 ≤ fullResponseWaveLayerMass γ := by
    rw [← hA.1.tsum_eq]
    exact tsum_nonneg (fun k => mul_nonneg (bankLayerWeight_nonneg k) (by positivity))
  have hfirst : 0 ≤ fullResponseWaveLayerFirst γ := by
    rw [← hA.2.tsum_eq]
    exact tsum_nonneg (fun k => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (bankLayerWeight_nonneg k)) (by positivity))
  have htail : 0 ≤ selectedRootExactMoment γ p 377 := by
    unfold selectedRootExactMoment
    apply tsum_nonneg
    intro n
    unfold selectedTailProbability
    positivity
  have hJ : 0 ≤ selectedJp γ p 377 := by
    unfold selectedJp
    positivity
  exact ⟨h0,hmass,hfirst,hJ,full_response_selected_wave_budget_nonneg γ p hp 0,
    full_response_selected_wave_budget_nonneg γ p hp 1⟩

/-- The corrected positive L0plus/L1plus profiles are nonnegative actual series. -/
theorem full_response_positive_layer_endpoint_signs : (0:ℝ) ≤ (invL0plus:ℝ) ∧ (0:ℝ) ≤ (invL1plus:ℝ) := by
  have hE (k : ℕ) : 0 ≤ fullResponseRootLayerEnvelope k :=
    (Real.sqrt_nonneg _).trans (full_response_root_layer_sqrt_le k)
  have hz : (0:ℝ) ≤ (invLayerZ:ℝ) := by norm_num [invLayerZ,invE,invGamma]
  constructor
  · rw [← full_response_root_layer_endpoint_profiles.1.tsum_eq]
    exact tsum_nonneg (fun k => mul_nonneg (hE k) (pow_nonneg hz _))
  · rw [← full_response_root_layer_endpoint_profiles.2.tsum_eq]
    exact tsum_nonneg (fun k => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hE k)) (pow_nonneg hz _))

end
end ASDExplicitGamma.Inverse
