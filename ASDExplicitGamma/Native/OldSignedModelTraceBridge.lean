module

public import ASDExplicitGamma.Native.OldSignedPhysicalTraceSeries

/-! Exact connection from the closed-cube physical heat observable to the
actual open-cube canonical OLD Hessian sum, including its true frame factor. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
noncomputable section

/-- The exact second directional chain rule for a linear restriction.
Adapted from the existing open-cube trace bridge. -/
theorem old_signed_second_directional_comp_linear
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (hf : ContDiff ℝ 2 f) (L : E →L[ℝ] F) (x v : E) :
    secondDirectionalDerivative (fun y => f (L y)) x v =
      secondDirectionalDerivative f (L x) (L v) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfirst (y : E) :
      fderiv ℝ (fun z => f (L z)) y = (fderiv ℝ f (L y)).comp L :=
    (hfd (L y)).hasFDerivAt.comp y L.hasFDerivAt |>.fderiv
  have hdir : (fun y => fderiv ℝ (fun z => f (L z)) y v) =
      fun y => fderiv ℝ f (L y) (L v) := by
    funext y
    rw [hfirst]
    rfl
  let g : F → ℝ := fun y => fderiv ℝ f y (L v)
  have hg : DifferentiableAt ℝ g (L x) :=
    ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
      contDiff_const).differentiable_one.differentiableAt
  have hsecond := hg.hasFDerivAt.comp x L.hasFDerivAt
  have hsecond' : fderiv ℝ (fun y : E => g (L y)) x =
      (fderiv ℝ g (L x)).comp L := by
    simpa only [Function.comp_def] using hsecond.fderiv
  unfold secondDirectionalDerivative
  rw [hdir]
  change fderiv ℝ (fun y => g (L y)) x v =
    fderiv ℝ (fun y => fderiv ℝ f y (L v)) (L x) (L v)
  rw [hsecond']
  rfl


/-- The normalized trace is C2 by its actual canonical finite-load decomposition. -/
theorem old_signed_trace_contDiff (m : ℤ) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) :
    ContDiff ℝ 2 (lemmaVTrace m nu sigma) := by
  have he : lemmaVTrace m nu sigma=(fun z =>
      (∑ c : BlockCoord 2,oldSignedCanonicalLoadEnergy m nu sigma hnu hsigma c z)-4) :=
    funext (old_signed_trace_eq_canonical_sum m nu sigma hnu hsigma)
  have hd (c : BlockCoord 2) : ContDiff ℝ 2 (oldSignedCanonicalLoadEnergy m nu sigma hnu hsigma c) :=
    responseFrameEnergyObservable_contDiff _ _ nu sigma hnu hsigma _
  rw [he]
  exact (ContDiff.sum (s := Finset.univ) (fun c _ => hd c)).sub contDiff_const

/-- The actual closed-cube q3 heat generator equals the complete physical
canonical OLD Hessian sum. The direction amplitude is sigma b, as required
by the normalized multiplier b; no covariance identification is assumed. -/
theorem old_signed_model_trace_generator_eq (m : ℤ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (b : ℝ) (L : {l : ℝ // 0<l})
    (x : C(closure (cubeSet (originCube 2 m)),ℝ)) :
    (1/2:ℝ)*modelCovarianceTrace (modelTraceObservable m nu sigma)
      (pureFluxMainCubeQ3Directions m (sigma*b) L) x=
      ∑' n : whiteBasisIndex,∑ c : BlockCoord 2,
        oldSignedPhysicalHessian (originCube 2 m) nu sigma hnu hsigma
          (pureFluxOpenResponseRestriction m x) (blockBasis c) b L n := by
  let R := pureFluxOpenResponseRestriction m
  have he : modelTraceObservable m nu sigma=(fun z => lemmaVTrace m nu sigma (R z)) :=
    funext (modelTraceObservable_eq_lemmaVTrace_openRestriction m nu sigma hnu hsigma)
  have ht : modelCovarianceTrace (modelTraceObservable m nu sigma)
      (pureFluxMainCubeQ3Directions m (sigma*b) L) x=
      modelCovarianceTrace (lemmaVTrace m nu sigma)
        (pureFluxMainCubeQ3ResponseCoefficient m (sigma*b) L) (R x) := by
    rw [he]
    unfold modelCovarianceTrace
    apply tsum_congr
    intro j
    rw [old_signed_second_directional_comp_linear _ (old_signed_trace_contDiff m nu sigma hnu hsigma) R]
    rw [main_q3_responseCoefficient_eq_restriction]
  rw [ht]
  exact old_signed_physical_trace_eq_covariance m nu sigma hnu hsigma (R x) b L

end
end ASDExplicitGamma.Native
