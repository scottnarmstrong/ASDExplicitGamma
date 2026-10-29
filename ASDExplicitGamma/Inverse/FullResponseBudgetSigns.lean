module

public import ASDExplicitGamma.Inverse.FullResponseEndpointRows

/-! Signs of the complete source budgets, before conversion to extended norm caps. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

theorem full_response_leading_budget_nonneg (γ p D : ℝ)
    (hγ : 0 ≤ γ) (hg : γ ≤ gammaZero) (hp : 0 ≤ p) (hD : 0 ≤ D) (a : Fin 3) :
    0 ≤ fullResponseTraceLeadingBudget γ p D a := by
  obtain ⟨hA,hM,hF,hJ,hW0,hW1⟩ := full_response_profile_signs γ p hg hp
  have hL0 := full_response_positive_layer_endpoint_signs.1
  have hL1 := full_response_positive_layer_endpoint_signs.2
  have hE : 0 ≤ rootEdelta .full := (Real.exp_pos _).le
  have hB := full_response_trace_baseline_nonneg
  have hS : 0 ≤ planarGradientCharge 40+1 := by unfold planarGradientCharge; positivity
  have hc1 : 0 ≤ fullResponseTraceC1 := by unfold fullResponseTraceC1 rootTau; positivity
  fin_cases a <;> simp [fullResponseTraceLeadingBudget,fullResponseIdentityWaveBudget,fullResponseActiveWaveBudget] <;> positivity

theorem full_response_error_budget_nonneg (γ p D : ℝ)
    (hγ : 0 ≤ γ) (hg : γ ≤ gammaZero) (hp : 0 ≤ p) (hD : 0 ≤ D) (b : Fin 4) :
    0 ≤ fullResponseTraceErrorBudget γ p D b := by
  have hE : 0 ≤ rootEdelta .full := (Real.exp_pos _).le
  have hc0 : 0 ≤ fullResponseTraceC0 := by unfold fullResponseTraceC0 rootTau; positivity
  have hc1 : 0 ≤ fullResponseTraceC1 := by unfold fullResponseTraceC1 rootTau; positivity
  have hD40 := (full_response_D4_budget_nonneg γ p hg).1
  have hD41 := (full_response_D4_budget_nonneg γ p hg).2
  have hZ : 0 ≤ densityEZ γ (planarGradientCharge 40) 339 := by
    rw [← (reset_density_EZ_hasSum γ (planarGradientCharge 40) hg 339).tsum_eq]
    apply tsum_nonneg
    intro hk
    unfold resetDensityEZBudget planarGradientCharge
    positivity
  have hmat : 0 ≤ fullResponseTraceMatrixBudget γ p D 377 := by
    rw [← (full_response_trace_matrix_budget_hasSum γ p D hg 377).tsum_eq]
    exact tsum_nonneg (full_response_trace_matrix_budget_term_nonneg γ p D hγ hp hD 377)
  have hk : 0 ≤ rootEdelta .full*fullResponseTraceC1*γ*(3:ℝ)^(2*γ*D)/2 := by positivity
  have hpcoef : 0 ≤ 40*(2*p+2) := by positivity
  fin_cases b
  · simpa [fullResponseTraceErrorBudget] using hmat
  · simpa [fullResponseTraceErrorBudget] using mul_nonneg (mul_nonneg hE hc0) hZ
  · simpa [fullResponseTraceErrorBudget] using
      mul_nonneg (mul_nonneg hk hD) (mul_nonneg hpcoef hD40)
  · simpa [fullResponseTraceErrorBudget] using mul_nonneg hk (mul_nonneg hpcoef hD41)

end
end ASDExplicitGamma.Inverse
