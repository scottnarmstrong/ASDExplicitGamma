module

public import ASDExplicitGamma.Inverse.BankHistoryPopulation
public import ASDExplicitGamma.Inverse.BankRootProfileArithmetic

/-! Numeric inverse-row caps for the conditional positive remainder histories. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ASDExplicitGamma.Numerics.Inverse
open scoped ENNReal

theorem bank_root_matrix_error_budget_nonneg (γ : ℝ) (r : RootRow) :
    0 ≤ rootMatrixErrorBudget γ 256 r := by
  unfold rootMatrixErrorBudget
  have hseries : 0 ≤ (∑' hk : ℕ × ℕ,
      Real.sqrt (bankLayerWeight hk.2) *
        (3:ℝ)^(2*γ*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)) *
        (3:ℝ)^(-((localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)+1))) := by
    apply tsum_nonneg
    intro hk
    positivity
  have hEd : 0 ≤ rootEdelta r := by unfold rootEdelta; positivity
  have hTau : 0 ≤ rootTau r := by cases r <;> norm_num [rootTau]
  have hEnvelope : 0 ≤ rootResponseEnvelope (rootTau r) := by
    unfold rootResponseEnvelope
    positivity
  positivity

theorem bank_root_density_error_budget_nonneg (γ : ℝ) (r : RootRow)
    (hγ : γ ≤ 17/50000) : 0 ≤ rootDensityErrorBudget γ r := by
  unfold rootDensityErrorBudget
  have hPower := bank_root_density_power_nonneg γ hγ (rootH0 r-38)
  have hEZ : 0 ≤ densityEZ γ (planarGradientCharge 40) (rootH0 r-38) := by
    unfold densityEZ
    have hhalf : 0 ≤ (3:ℝ)^(1/2:ℝ) := Real.rpow_nonneg (by norm_num) _
    have hpow : 0 ≤ (3:ℝ)^(2*(1/2:ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hfactor : 0 ≤ 1+(3:ℝ)^(1/2:ℝ)+(3:ℝ)^(2*(1/2:ℝ)) := by
      exact add_nonneg (add_nonneg (by norm_num) hhalf) hpow
    exact mul_nonneg (mul_nonneg (by norm_num [planarGradientCharge]) hfactor) hPower
  have hEd : 0 ≤ rootEdelta r := by unfold rootEdelta; positivity
  have hTau : 0 ≤ rootTau r := by cases r <;> norm_num [rootTau]
  have hEnvelope : 0 ≤ rootResponseEnvelope (6*rootTau r) := by
    unfold rootResponseEnvelope
    positivity
  exact mul_nonneg (mul_nonneg hEd hEnvelope) hEZ

theorem bank_root_selected_remainder_L256_of_profile
    (M : ABKModel 2) (Q : TriadicCube 2) (m J : ℤ) (weights : ℤ → ℝ)
    (r : RootRow) (rho : ℝ)
    (hγ : M.gamma ≤ 17/50000)
    (hPointwise : PointwiseRootConclusion M Q m J weights r)
    (hSelected : FixedSelectedHeightConclusion M Q r)
    (hProfile : rootLi M.gamma r * selectedRootTiny (rootH0 r) +
      (rootMatrixErrorBudget M.gamma 256 r +
        rootDensityErrorBudget M.gamma r) ≤ rho) :
    eLpNorm (bankRootSelectedRemainder M Q r) 256
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal rho := by
  have hRemainder := bank_root_selected_remainder_L256 M Q m J weights r
    hPointwise hSelected
  have hLi : 0 ≤ rootLi M.gamma r := bank_root_Li_nonneg M.gamma r
  have hTiny : 0 ≤ selectedRootTiny (rootH0 r) := by
    unfold selectedRootTiny
    split <;> positivity
  have hBudget : 0 ≤ rootMatrixErrorBudget M.gamma 256 r +
      rootDensityErrorBudget M.gamma r :=
    add_nonneg (bank_root_matrix_error_budget_nonneg M.gamma r)
      (bank_root_density_error_budget_nonneg M.gamma r hγ)
  have hSum := ENNReal.ofReal_add
    (mul_nonneg hLi hTiny) hBudget
  rw [← hSum] at hRemainder
  exact hRemainder.trans (ENNReal.ofReal_le_ofReal hProfile)

end ASDExplicitGamma.Inverse
