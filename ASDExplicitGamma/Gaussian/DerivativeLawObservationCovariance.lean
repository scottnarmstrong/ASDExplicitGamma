module

public import ASDExplicitGamma.Gaussian.DerivativeLawStored
public import ASDExplicitGamma.Gaussian.DerivativeLawCovarianceDerivative

/-! Actual observation derivatives commute with Gaussian covariance integration. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization Algsuperdiff.Frozen.Assumptions MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- Apply the ordinary directional partial derivatives specified by an observation. -/
def shellObservationApply : ShellDerivativeObservation → (Vec 2 → ℝ) → ℝ
  | .value x, f => f x
  | .first x v, f => deriv (fun t : ℝ => f (x+t • v)) 0
  | .second x v w, f => deriv (fun t : ℝ => deriv (fun s : ℝ => f (x+t • w+s • v)) 0) 0

 theorem shellScalarValue_line_hasDerivAt (j : ShellField 2) (x v : Vec 2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => shellScalarValue j (x+s • v)) (shellScalarDerivative j (x+t • v) v) t := by
  have hl : HasDerivAt (fun s : ℝ => x+s • v) v t := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const v).const_add x
  simpa only [Function.comp_def] using! (shellScalarValue_hasFDerivAt j (x+t • v)).comp_hasDerivAt t hl

 theorem shellScalarFirst_line_hasDerivAt (j : ShellField 2) (x v w : Vec 2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => shellScalarFirst v j (x+s • w)) (shellScalarFirstDerivative v j (x+t • w) w) t := by
  have hl : HasDerivAt (fun s : ℝ => x+s • w) w t := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id t).smul_const w).const_add x
  simpa only [Function.comp_def] using! (shellScalarFirst_hasFDerivAt v j (x+t • w)).comp_hasDerivAt t hl

 theorem IsCenteredGaussianFamily.sum_reindex {Ω I A B : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : I → Ω → ℝ} (hX : IsCenteredGaussianFamily μ X) (f : A → I) (g : B → I) :
    IsCenteredGaussianFamily μ (Sum.elim (fun a => X (f a)) (fun b => X (g b))) := by
  have heq : Sum.elim (fun a => X (f a)) (fun b => X (g b)) = fun s => X (Sum.elim f g s) := by
    funext s ω
    cases s <;> rfl
  rw [heq]
  exact hX.comp (Sum.elim f g)

 theorem shellValue_covariance_line_hasDerivAt (μ : Measure (ShellField 2)) [IsProbabilityMeasure μ]
    (hg : IsCenteredGaussianFamily μ shellDerivativeEval) (p : ShellDerivativeObservation) (x v : Vec 2) :
    HasDerivAt (fun t : ℝ => ∫ j, shellScalarValue j (x+t • v)*shellDerivativeEval p j ∂μ)
      (∫ j, shellDerivativeEval (.first x v) j*shellDerivativeEval p j ∂μ) 0 := by
  apply hasDerivAt_integral_product_of_gaussian μ (fun t j => shellScalarValue j (x+t • v))
    (shellDerivativeEval p) (shellDerivativeEval (.first x v)) 0
  · exact hg.sum_reindex (fun _ : Unit => p) (fun t => .value (x+t • v))
  · exact (shellDerivativeEval_continuous _).measurable.aemeasurable
  · exact Filter.Eventually.of_forall fun j => by
      simpa only [zero_smul, add_zero, shellDerivativeEval, shellScalarFirst] using shellScalarValue_line_hasDerivAt j x v 0

 theorem shellFirst_covariance_line_hasDerivAt (μ : Measure (ShellField 2)) [IsProbabilityMeasure μ]
    (hg : IsCenteredGaussianFamily μ shellDerivativeEval) (p : ShellDerivativeObservation) (x v w : Vec 2) :
    HasDerivAt (fun t : ℝ => ∫ j, shellScalarFirst v j (x+t • w)*shellDerivativeEval p j ∂μ)
      (∫ j, shellDerivativeEval (.second x v w) j*shellDerivativeEval p j ∂μ) 0 := by
  apply hasDerivAt_integral_product_of_gaussian μ (fun t j => shellScalarFirst v j (x+t • w))
    (shellDerivativeEval p) (shellDerivativeEval (.second x v w)) 0
  · exact hg.sum_reindex (fun _ : Unit => p) (fun t => .first (x+t • w) v)
  · exact (shellDerivativeEval_continuous _).measurable.aemeasurable
  · exact Filter.Eventually.of_forall fun j => by
      simpa only [zero_smul, add_zero, shellDerivativeEval, shellScalarFirst] using shellScalarFirst_line_hasDerivAt j x v w 0

/-- Both stored derivatives may be passed through covariance integration;
Gaussian covariance convergence proves this without an integrable derivative bound. -/
theorem shellObservationApply_integral_product (μ : Measure (ShellField 2)) [IsProbabilityMeasure μ]
    (hg : IsCenteredGaussianFamily μ shellDerivativeEval) (o p : ShellDerivativeObservation) :
    shellObservationApply o (fun x => ∫ j, shellScalarValue j x*shellDerivativeEval p j ∂μ) =
      ∫ j, shellDerivativeEval o j*shellDerivativeEval p j ∂μ := by
  cases o with
  | value x => rfl
  | first x v => exact (shellValue_covariance_line_hasDerivAt μ hg p x v).deriv
  | second x v w =>
      have hi (t : ℝ) : deriv (fun s : ℝ => ∫ j, shellScalarValue j (x+t • w+s • v)*shellDerivativeEval p j ∂μ) 0 =
          ∫ j, shellScalarFirst v j (x+t • w)*shellDerivativeEval p j ∂μ :=
        (shellValue_covariance_line_hasDerivAt μ hg p (x+t • w) v).deriv
      change deriv (fun t : ℝ => deriv (fun s : ℝ => ∫ j, shellScalarValue j (x+t • w+s • v)*shellDerivativeEval p j ∂μ) 0) 0 = _
      simp_rw [hi]
      exact (shellFirst_covariance_line_hasDerivAt μ hg p x v w).deriv

end
end ASDExplicitGamma.Gaussian
