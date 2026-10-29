module

public import ASDExplicitGamma.Gaussian.DerivativeLawValueCovariance
public import ASDExplicitGamma.Gaussian.DerivativeLawObservationCovariance

/-! Complete joint Gaussian and differentiated covariance law of the frozen q3 C2 shell. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- The actual x/y directional derivatives of the fully scaled product-q3 kernel. -/
def q3ShellDerivativeCovariance (M : ABKModel 2) (h : ℝ) (k : ℤ)
    (o p : ShellDerivativeObservation) : ℝ :=
  shellObservationApply o (fun x => shellObservationApply p (fun y => q3ShellCovariance M h k x y))

/-- GA-DERIVATIVE-LAW covariance clause, for every integer shell level and
all mixed stored value/first/second derivative observations. -/
theorem q3Shell_stored_derivative_covariance (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (k : ℤ)
    (o p : ShellDerivativeObservation) :
    (∫ j, shellDerivativeEval o j*shellDerivativeEval p j ∂(ShellField.shellMarginalLaw M.P k).toMeasure) =
      q3ShellDerivativeCovariance M h k o p := by
  let μ := (ShellField.shellMarginalLaw M.P k).toMeasure
  have hg := q3Shell_stored_derivatives_gaussian M h hM k
  have hcomm (X Y : ShellField 2 → ℝ) : (∫ j, X j*Y j ∂μ) = ∫ j, Y j*X j ∂μ := by
    congr 1
    funext j
    exact mul_comm _ _
  have hp (x : Vec 2) : (∫ j, shellScalarValue j x*shellDerivativeEval p j ∂μ) =
      shellObservationApply p (fun y => ∫ j, shellScalarValue j x*shellScalarValue j y ∂μ) := by
    rw [hcomm (fun j => shellScalarValue j x) (shellDerivativeEval p)]
    change (∫ j, shellDerivativeEval p j*shellDerivativeEval (.value x) j ∂μ) = _
    rw [← shellObservationApply_integral_product μ hg p (.value x)]
    apply congrArg (shellObservationApply p)
    funext y
    exact hcomm (fun j => shellScalarValue j y) (fun j => shellScalarValue j x)
  have hf : (fun x => ∫ j, shellScalarValue j x*shellDerivativeEval p j ∂μ) =
      fun x => shellObservationApply p (fun y => q3ShellCovariance M h k x y) := by
    funext x
    rw [hp]
    apply congrArg (shellObservationApply p)
    funext y
    exact q3Shell_value_covariance M h hM k x y
  rw [← shellObservationApply_integral_product μ hg o p, hf]
  rfl

/-- GA-DERIVATIVE-LAW in one statement: the joint finite Gaussian law
and the exact differentiated covariance, without any derivative-law premise. -/
theorem q3Shell_derivative_law (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (k : ℤ) :
    IsCenteredGaussianFamily (ShellField.shellMarginalLaw M.P k).toMeasure shellDerivativeEval ∧
    ∀ o p : ShellDerivativeObservation,
      (∫ j, shellDerivativeEval o j*shellDerivativeEval p j ∂(ShellField.shellMarginalLaw M.P k).toMeasure) =
        q3ShellDerivativeCovariance M h k o p :=
  ⟨q3Shell_stored_derivatives_gaussian M h hM k, q3Shell_stored_derivative_covariance M h hM k⟩

end
end ASDExplicitGamma.Gaussian
