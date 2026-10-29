module

public import ASDExplicitGamma.Inverse.ResponseCoefficients
public import ASDExplicitGamma.Inverse.RawInverseHistory
public import ASDExplicitGamma.Triadic.SensitivityODELambda

/-! The initial sensitivity lambda is the actual old completed-cutoff lambda
on every genuine descendant, in the same true frame. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

/-- On all descendants, the time-zero sensitivity family is exactly the
actual old coefficient family. Tietze values outside the root are irrelevant. -/
theorem initial_sensitivity_lambda_eq (M : ABKModel 2) (Q : TriadicCube 2) (n J : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (u : ℝ) :
    sensitivityPathLambdaInverse M.nu M.nu_pos (oldResponseCoefficient Q n ω)
      (laterResponseCoefficient Q n J weights ω) u 0 =
      (Book.Ch02.lambdaSqFinite Q u 2
        (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField (Cutoff.coefficientCutoff M.nu n ω)
          (Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M n ω)))⁻¹ := by
  unfold sensitivityPathLambdaInverse
  apply congrArg (fun z : ℝ => z⁻¹)
  apply sensitivity_lambdaSqFinite_eq_of_descendant_aeeq
  intro j R hR
  change (sensitivityBaseRegField M.nu
    (sensitivityResponseCoefficientPath (oldResponseCoefficient Q n ω)
      (laterResponseCoefficient Q n J weights ω) 0)).toFun =ᵐ[volumeMeasureOn (openCubeSet R)]
      (Cutoff.coefficientCutoff M.nu n ω).toFun
  simp only [sensitivityResponseCoefficientPath,zero_smul,add_zero]
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
  exact old_response_coefficient_represents M Q n ω (openCubeSet_subset_of_mem_descendantsAtDepth hR hx)

/-- The actual good history discharges the initial inverse lambda bound of
the sensitivity ODE theorem, without a lambda or response premise. -/
theorem good_initial_sensitivity_lambda_bound (M : ABKModel 2) (Q : TriadicCube 2)
    (n J : ℤ) (weights : ℤ → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∈ clippedCellGoodEvent M n Q τ) :
    (Annealed.sigmaBar M n:ℝ)*sensitivityPathLambdaInverse M.nu M.nu_pos
      (oldResponseCoefficient Q n ω) (laterResponseCoefficient Q n J weights ω) (1/4) 0 ≤ 2*(1+τ) := by
  rw [initial_sensitivity_lambda_eq]
  exact good_inverse_lambda_quarter_bound M n Q τ hτ ω hgood

end
end ASDExplicitGamma.Inverse
