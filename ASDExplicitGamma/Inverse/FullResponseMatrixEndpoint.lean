module

public import ASDExplicitGamma.Inverse.FullResponseResetEndpoint
public import ASDExplicitGamma.Inverse.FullResponseParameterEndpoint

/-! Complete full-response matrix errors consume the literal M0/350 M0 payments. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- Both retained complete reset sums are nonnegative. -/
theorem full_response_retained_sums_nonneg (a ρ : ℝ) (C : ℕ) (hdecay : a < ρ) :
    0 ≤ densityResetPowerSum a ρ C ∧ 0 ≤ densityResetFirstPowerSum a ρ C := by
  constructor
  · rw [← (density_reset_power_hasSum a ρ hdecay C).tsum_eq]
    exact tsum_nonneg (fun _ => by positivity)
  · rw [← (density_reset_first_power_hasSum a ρ hdecay C).tsum_eq]
    exact tsum_nonneg (fun _ => by positivity)

/-- Generic consumption of the actual finite-order matrix prefactor and
both full retained M4 depth moments. -/
theorem full_response_matrix_budget_endpoint (γ p D MC : ℝ)
    (hγ : 0 ≤ γ) (hg : γ ≤ gammaZero) (hp : 0 ≤ p) (hD : 0 ≤ D)
    (hMC : 256*Real.sqrt p*rootResponseEnvelope (rootTau .full) ≤ MC) :
    fullResponseTraceMatrixBudget γ p D 377 ≤
      (invFull128Ed:ℝ)*MC*(2*(invFull128M0:ℝ)+
        80*(p+2)*γ*(3:ℝ)^(2*γ*D)*(D*(invFull128M0:ℝ)+350*(invFull128M0:ℝ))) := by
  have hg' : γ ≤ 17/50000 := hg
  have h2 := full_response_matrix_reset_endpoint (2*γ) (by change 2*γ ≤ 4*(17/50000); linarith only [hg'])
  have h4 := full_response_matrix_reset_endpoint (4*γ) (by change 4*γ ≤ 4*(17/50000); linarith only [hg'])
  have hn2 := (full_response_retained_sums_nonneg (2*γ) 1 339 (by linarith only [hg'])).1
  have hn4 := full_response_retained_sums_nonneg (4*γ) 1 339 (by linarith only [hg'])
  have he0 : 0 ≤ rootResponseEnvelope (rootTau .full) := by
    unfold rootResponseEnvelope rootTau
    positivity
  have hpre0 : 0 ≤ 256*Real.sqrt p*rootResponseEnvelope (rootTau .full) := by positivity
  have hMC0 := hpre0.trans hMC
  have hcoef : 0 ≤ 80*(p+2)*γ*(3:ℝ)^(2*γ*D) := by positivity
  have hinside := add_le_add (mul_le_mul_of_nonneg_left h4.1 hD) h4.2
  have hbracket := add_le_add (mul_le_mul_of_nonneg_left h2.1 (by norm_num : (0:ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hinside hcoef)
  have hbracket0 : 0 ≤ 2*densityResetPowerSum (2*γ) 1 339+
      80*(p+2)*γ*(3:ℝ)^(2*γ*D)*
        (D*densityResetPowerSum (4*γ) 1 339+densityResetFirstPowerSum (4*γ) 1 339) :=
    add_nonneg (mul_nonneg (by norm_num) hn2)
      (mul_nonneg hcoef (add_nonneg (mul_nonneg hD hn4.1) hn4.2))
  have hprod := mul_le_mul hMC hbracket hbracket0 hMC0
  have hEd0 : (0:ℝ) ≤ (invFull128Ed:ℝ) := by
    norm_num [invFull128Ed,invFull128Delta,invE,invFullTau]
  have hh := mul_le_mul full_response_Edelta_endpoint hprod
    (mul_nonneg hpre0 hbracket0) hEd0
  dsimp only [fullResponseTraceMatrixBudget]
  norm_num only [Nat.reduceSub]
  convert hh using 1 <;> ring

/-- Order-64 matrix budget using its separate MC64. -/
theorem full_response_matrix_budget64 (γ D : ℝ) (hγ : 0 ≤ γ) (hg : γ ≤ gammaZero) (hD : 0 ≤ D) :
    fullResponseTraceMatrixBudget γ 64 D 377 ≤
      (invFull64Ed:ℝ)*(invFull64MC:ℝ)*(2*(invFull64M0:ℝ)+
        80*(64+2)*γ*(3:ℝ)^(2*γ*D)*(D*(invFull64M0:ℝ)+350*(invFull64M0:ℝ))) := by
  have hh := full_response_matrix_budget_endpoint γ 64 D (invFull64MC:ℝ)
    hγ hg (by norm_num) hD full_response_matrix_prefactor64
  simpa only [invFull128Ed,invFull64Ed,invFull128Delta,invFull64Delta,invFull128M0,invFull64M0] using hh

/-- Order-128 matrix budget using MC128 and the same literal M0 supplier. -/
theorem full_response_matrix_budget128 (γ D : ℝ) (hγ : 0 ≤ γ) (hg : γ ≤ gammaZero) (hD : 0 ≤ D) :
    fullResponseTraceMatrixBudget γ 128 D 377 ≤
      (invFull128Ed:ℝ)*(invFull128MC:ℝ)*(2*(invFull128M0:ℝ)+
        80*(128+2)*γ*(3:ℝ)^(2*γ*D)*(D*(invFull128M0:ℝ)+350*(invFull128M0:ℝ))) :=
  full_response_matrix_budget_endpoint γ 128 D (invFull128MC:ℝ)
    hγ hg (by norm_num) hD full_response_matrix_prefactor128

end
end ASDExplicitGamma.Inverse
