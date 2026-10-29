module

public import ASDExplicitGamma.Inverse.RootDefinitions
public import ASDExplicitGamma.Inverse.AssemblyTraceMatrixBudget
public import ASDExplicitGamma.Inverse.StoppedDensityResetPowers

/-! Fixed full-response sheared-matrix error envelopes, including the depth moment. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
noncomputable section

/-- The exact clocked matrix envelope after discarding only sqrt(v)≤1. -/
def fullResponseTraceMatrixBudgetTerm (γ p D : ℝ) (H0 : ℕ) (hk : ℕ × ℕ) : ℝ :=
  let x := (localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)
  ((rootEdelta .full)*256*Real.sqrt p*rootResponseEnvelope (rootTau .full))*
    (2*((3:ℝ)^(2*γ*x)*(3:ℝ)^(-(x+1)))+
      80*(p+2)*γ*(3:ℝ)^(2*γ*D)*
        (D*((3:ℝ)^(4*γ*x)*(3:ℝ)^(-(x+1)))+
          x*((3:ℝ)^(4*γ*x)*(3:ℝ)^(-(x+1)))))

/-- Closed complete source trace-matrix error budget. -/
def fullResponseTraceMatrixBudget (γ p D : ℝ) (H0 : ℕ) : ℝ :=
  ((rootEdelta .full)*256*Real.sqrt p*rootResponseEnvelope (rootTau .full))*
    (2*densityResetPowerSum (2*γ) 1 (H0-38)+
      80*(p+2)*γ*(3:ℝ)^(2*γ*D)*
        (D*densityResetPowerSum (4*γ) 1 (H0-38)+
          densityResetFirstPowerSum (4*γ) 1 (H0-38)))

theorem full_response_trace_matrix_budget_term_nonneg (γ p D : ℝ)
    (hγ : 0 ≤ γ) (hp : 0 ≤ p) (hD : 0 ≤ D) (H0 : ℕ) (hk : ℕ × ℕ) :
    0 ≤ fullResponseTraceMatrixBudgetTerm γ p D H0 hk := by
  have hs : 0 ≤ rootEdelta .full := (Real.exp_pos _).le
  have hτ : 0 ≤ (rootTau .full) := by norm_num [rootTau]
  unfold fullResponseTraceMatrixBudgetTerm rootResponseEnvelope
  positivity

/-- Both complete indices converge, retaining the source's first x moment. -/
theorem full_response_trace_matrix_budget_hasSum (γ p D : ℝ) (hγ : γ ≤ gammaZero) (H0 : ℕ) :
    HasSum (fullResponseTraceMatrixBudgetTerm γ p D H0) (fullResponseTraceMatrixBudget γ p D H0) := by
  have hg : γ ≤ 17/50000 := hγ
  have h2 := density_reset_power_hasSum (2*γ) 1 (by linarith only [hg]) (H0-38)
  have h4 := density_reset_power_hasSum (4*γ) 1 (by linarith only [hg]) (H0-38)
  have hf := density_reset_first_power_hasSum (4*γ) 1 (by linarith only [hg]) (H0-38)
  have hh := ((h2.mul_left 2).add (((h4.mul_left D).add hf).mul_left
    (80*(p+2)*γ*(3:ℝ)^(2*γ*D)))).mul_left
      ((rootEdelta .full)*256*Real.sqrt p*rootResponseEnvelope (rootTau .full))
  convert hh using 1
  · funext hk
    simp only [fullResponseTraceMatrixBudgetTerm,neg_one_mul]
  · rfl


end
end ASDExplicitGamma.Inverse
