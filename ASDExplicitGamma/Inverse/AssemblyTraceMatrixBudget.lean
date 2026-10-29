module

public import ASDExplicitGamma.Inverse.AssemblyShearedLayers
public import ASDExplicitGamma.Inverse.AssemblyPositiveLayer
public import ASDExplicitGamma.Inverse.StoppedDensityResetPowers

/-! Complete sheared-matrix error envelopes, including the depth moment. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
noncomputable section

/-- The exact clocked matrix envelope after discarding only sqrt(v)≤1. -/
def assemblyTraceMatrixBudgetTerm (γ p D : ℝ) (H0 : ℕ) (hk : ℕ × ℕ) : ℝ :=
  let x := (localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)
  (rootAssemblySensitivity*256*Real.sqrt p*rootResponseEnvelope resetAllOrderTau)*
    (2*((3:ℝ)^(2*γ*x)*(3:ℝ)^(-(x+1)))+
      80*(p+2)*γ*(3:ℝ)^(2*γ*D)*
        (D*((3:ℝ)^(4*γ*x)*(3:ℝ)^(-(x+1)))+
          x*((3:ℝ)^(4*γ*x)*(3:ℝ)^(-(x+1)))))

/-- Closed complete source trace-matrix error budget. -/
def assemblyTraceMatrixBudget (γ p D : ℝ) (H0 : ℕ) : ℝ :=
  (rootAssemblySensitivity*256*Real.sqrt p*rootResponseEnvelope resetAllOrderTau)*
    (2*densityResetPowerSum (2*γ) 1 (H0-38)+
      80*(p+2)*γ*(3:ℝ)^(2*γ*D)*
        (D*densityResetPowerSum (4*γ) 1 (H0-38)+
          densityResetFirstPowerSum (4*γ) 1 (H0-38)))

theorem assembly_trace_matrix_budget_term_nonneg (γ p D : ℝ)
    (hγ : 0 ≤ γ) (hp : 0 ≤ p) (hD : 0 ≤ D) (H0 : ℕ) (hk : ℕ × ℕ) :
    0 ≤ assemblyTraceMatrixBudgetTerm γ p D H0 hk := by
  have hs := root_assembly_sensitivity_pos.le
  have hτ : 0 ≤ resetAllOrderTau := by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  unfold assemblyTraceMatrixBudgetTerm rootResponseEnvelope
  positivity

/-- Both complete indices converge, retaining the source's first x moment. -/
theorem assembly_trace_matrix_budget_hasSum (γ p D : ℝ) (hγ : γ ≤ gammaZero) (H0 : ℕ) :
    HasSum (assemblyTraceMatrixBudgetTerm γ p D H0) (assemblyTraceMatrixBudget γ p D H0) := by
  have hg : γ ≤ 17/50000 := hγ
  have h2 := density_reset_power_hasSum (2*γ) 1 (by linarith only [hg]) (H0-38)
  have h4 := density_reset_power_hasSum (4*γ) 1 (by linarith only [hg]) (H0-38)
  have hf := density_reset_first_power_hasSum (4*γ) 1 (by linarith only [hg]) (H0-38)
  have hh := ((h2.mul_left 2).add (((h4.mul_left D).add hf).mul_left
    (80*(p+2)*γ*(3:ℝ)^(2*γ*D)))).mul_left
      (rootAssemblySensitivity*256*Real.sqrt p*rootResponseEnvelope resetAllOrderTau)
  convert hh using 1
  · funext hk
    simp only [assemblyTraceMatrixBudgetTerm,neg_one_mul]
  · rfl

/-- The displayed wave bracket splits into its complete power and first-moment sums. -/
theorem assembly_trace_matrix_envelope_factor (γ p D x a : ℝ) :
    a*((3:ℝ)^(2*γ*x)*(3:ℝ)^(-(x+1)))*
      (2+80*(p+2)*(γ*(D+x)*(3:ℝ)^(2*γ*(D+x)))) =
    a*(2*((3:ℝ)^(2*γ*x)*(3:ℝ)^(-(x+1)))+
      80*(p+2)*γ*(3:ℝ)^(2*γ*D)*
        (D*((3:ℝ)^(4*γ*x)*(3:ℝ)^(-(x+1)))+
          x*((3:ℝ)^(4*γ*x)*(3:ℝ)^(-(x+1))))) := by
  have hp : (3:ℝ)^(2*γ*(D+x)) = (3:ℝ)^(2*γ*D)*(3:ℝ)^(2*γ*x) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 1
    ring
  have hsq : (3:ℝ)^(4*γ*x) = ((3:ℝ)^(2*γ*x))^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    congr 1
    norm_num
    ring
  rw [hp,hsq]
  ring

end
end ASDExplicitGamma.Inverse
