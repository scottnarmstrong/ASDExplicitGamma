module

public import ASDExplicitGamma.Native.ParentBoundaryInverseBudgetModel
public import ASDExplicitGamma.Native.ParentBoundaryInverseLinearReturn

/-! Actual signed inverse-cost return into the sixteen source panel setups,
including the full smaller-gamma ray and its fixed correlated reserve. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

private theorem inverse_budget_nonneg (j : Fin 16) :
    0≤parentBoundaryInverseYBudget (j.val+1) ∧
      0≤parentBoundaryInverseKBudget (j.val+1) := by
  fin_cases j <;> decide +kernel

/-- On every actual completed parent band, the signed inverse integral
fits the EXACT real inverse-cost output of its source setup, proportionally
in theta. Only the source model and strict-past native states are hypotheses. -/
theorem parent_boundary_actual_inverse_setup_return
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (m : ℤ)
    (hpast : ∀ k<m,nativeInductionState M h k) (j : Fin 16) :
    let height := j.val+1
    let n := m-(height:ℤ)
    (∫ t in (0:ℝ)..1,-parentBoundaryBandDirichletEnergy M h n height*
      (parentBoundaryBandInverseMean M n height t-2))≤
        theta M*parentBoundarySetupInverseCost j := by
  intro height n
  have hh : height≤16 := by dsimp [height]; omega
  have hh0 : 1≤height := by dsimp [height]; omega
  have hn : n<m := by dsimp [n]; omega
  have hstate := hpast n hn
  have hpastn : ∀ k<n,nativeInductionState M h k := fun k hk => hpast k (hk.trans hn)
  let Y := parentBoundaryBandDirichletEnergy M h n height
  let kappa := mainKappa (parentBoundaryBandInverseClock M h n height)
  have hi := parent_boundary_actual_inverse_linear_integral M h hM hg n height hh0 hpastn
  have hY := parent_boundary_model_inverse_y_budget M h hg n height hh hstate
  have hk := parent_boundary_model_inverse_kappa_budget M h hg n height hh hstate
  have hY0 : (0:ℝ)≤(parentBoundaryInverseYBudget height:ℝ) := by
    exact_mod_cast (inverse_budget_nonneg j).1
  have hK0 : (0:ℝ)≤(parentBoundaryInverseKBudget height:ℝ) := by
    exact_mod_cast (inverse_budget_nonneg j).2
  have htheta0 : 0≤theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have htheta1 : theta M≤1 := (div_le_one (by norm_num [gammaZero])).mpr hg
  have hk0 : 0≤kappa := mul_nonneg
    (parent_boundary_inverse_band_clock_nonneg M h n height) (sq_nonneg mainBeta)
  have hk1 : kappa≤(parentBoundaryInverseKBudget height:ℝ) :=
    hk.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right htheta1 hK0)
  have hrho : 0≤2+mainRho := by unfold mainRho mainBeta mainEpsNew; positivity
  have hprod := mul_le_mul hY hk1 hk0 (mul_nonneg htheta0 hY0)
  have hscaled := mul_le_mul_of_nonneg_right hprod (div_nonneg hrho (by norm_num : (0:ℝ)≤2))
  have hRho : mainRho=(parentBoundaryInverseRhoBudget:ℝ) := by
    norm_num [mainRho,mainBeta,mainEpsNew,parentBoundaryInverseRhoBudget]
  have hcost : (parentBoundaryInverseCostBudget height:ℝ)=
      (parentBoundaryInverseYBudget height:ℝ)*(2+mainRho)*
        (parentBoundaryInverseKBudget height:ℝ)/2 := by
    unfold parentBoundaryInverseCostBudget
    push_cast
    rw [←hRho]
  have hpay : Y*(2+mainRho)*kappa/2≤theta M*(parentBoundaryInverseCostBudget height:ℝ) := by
    rw [hcost]
    convert hscaled using 1 <;> ring
  have hnum : (parentBoundaryInverseCostBudget height:ℝ)≤
      (parentBoundarySetupInverseLower j:ℝ) := by
    exact_mod_cast parent_boundary_inverse_budget_numeric j
  exact (hi.trans hpay).trans (mul_le_mul_of_nonneg_left
    (hnum.trans (parent_boundary_inverse_setup_lower j)) htheta0)

end
end ASDExplicitGamma.Native
