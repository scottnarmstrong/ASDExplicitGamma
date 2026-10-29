module

public import ASDExplicitGamma.Native.OldSignedInverseLinearReturn
public import ASDExplicitGamma.Native.ParentBoundaryInverseBudgetModel
public import ASDExplicitGamma.Numerics.Native.SetupQ1001Proof

/-! The full-variance signed inverse return fits the exact frozen q1 allocation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Triadic Main Inverse Algsuperdiff.Section3
open Numerics.Native
noncomputable section

/-- A rational upper allocation for the retained full-variance inverse cost. -/
def oldSignedQ1InverseBudget : ℚ := parentBoundaryVarianceBudget 1*
  (2+parentBoundaryInverseRhoBudget)*parentBoundaryInverseKBudget 1/2

/-- The unchanged q1 setup pays the complete signed inverse allocation. -/
theorem old_signed_q1_inverse_budget_numeric :
    oldSignedQ1InverseBudget≤nativeSetupQ1001InvcostI.lo := by decide +kernel

/-- The actual signed inverse integral is paid with its full variance,
with no inverse-flow or bank estimate left as a premise. -/
theorem old_signed_q1_inverse_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) :
    let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
    (∫ t in (0:ℝ)..1,-b^2*(parentBoundaryBandInverseMean M n 1 t-2))≤
      theta M*nativeSetupQ1001InvcostR := by
  intro b
  let k := mainKappa (parentBoundaryBandInverseClock M h n 1)
  have hi := old_signed_actual_inverse_linear_integral M h hM hg n 1 (by norm_num)
    (fun l hl => hpast l hl.le) (b^2) (sq_nonneg b)
  have hv : b^2≤theta M*(parentBoundaryVarianceBudget 1:ℝ) := by
    simpa only [b,div_pow,Nat.cast_one] using parent_boundary_model_shell_variance_budget
      M h hg n 1 1 (by norm_num) le_rfl (hpast n le_rfl)
  have hk := parent_boundary_model_inverse_kappa_budget M h hg n 1 (by norm_num) (hpast n le_rfl)
  have htheta0 : 0≤theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have htheta1 : theta M≤1 := (div_le_one (by norm_num [gammaZero])).mpr hg
  have hK0 : (0:ℝ)≤(parentBoundaryInverseKBudget 1:ℝ) := by norm_num [parentBoundaryInverseKBudget,parentBoundaryVarianceBudget]
  have hk1 : k≤(parentBoundaryInverseKBudget 1:ℝ) := hk.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right htheta1 hK0)
  have hk0 : 0≤k := mul_nonneg (parent_boundary_inverse_band_clock_nonneg M h n 1) (sq_nonneg mainBeta)
  have hv0 : (0:ℝ)≤(parentBoundaryVarianceBudget 1:ℝ) := by norm_num [parentBoundaryVarianceBudget]
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul hv hk1 hk0 (mul_nonneg htheta0 hv0))
    (show 0≤(2+mainRho)/2 by unfold mainRho mainBeta mainEpsNew; positivity)
  have hcost : b^2*(2+mainRho)*k/2≤theta M*(oldSignedQ1InverseBudget:ℝ) := by
    have hr : mainRho=(parentBoundaryInverseRhoBudget:ℝ) := by
      norm_num [mainRho,mainBeta,mainEpsNew,parentBoundaryInverseRhoBudget]
    unfold oldSignedQ1InverseBudget
    push_cast
    rw [←hr]
    convert hh using 1 <;> ring
  have hnum : (oldSignedQ1InverseBudget:ℝ)≤nativeSetupQ1001InvcostR := by
    exact (Rat.cast_le.mpr old_signed_q1_inverse_budget_numeric).trans (nativeSetupQ1001_sound 0).1
  exact (hi.trans hcost).trans (mul_le_mul_of_nonneg_left hnum htheta0)

end
end ASDExplicitGamma.Native
