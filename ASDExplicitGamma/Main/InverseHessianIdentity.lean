module

public import ASDExplicitGamma.Main.InverseObservable
public import ASDExplicitGamma.Inverse.PureFluxGeneratorSource
public import ASDExplicitGamma.Gaussian.CovarianceTrace

/-! Exact covariance-Hessian expansion of the fixed-frame inverse trace into
the two actual pure-flux affine response loads. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Response ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
open scoped BigOperators

private theorem mainInverse_fderiv_fderiv_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
  have hfdF : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfdG : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hfirst : (fun y => fderiv ℝ (fun z => f z + g z) y) =
      fun y => fderiv ℝ f y + fderiv ℝ g y := by
    funext y
    exact fderiv_fun_add (hfdF y) (hfdG y)
  have hsecondF : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable_one
  have hsecondG : Differentiable ℝ (fun y => fderiv ℝ g y) :=
    (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable_one
  change fderiv ℝ (fun y => fderiv ℝ (fun z => f z + g z) y) x = _
  rw [hfirst, fderiv_fun_add (hsecondF x) (hsecondG x)]

private theorem mainInverse_modelCovarianceTrace_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : ℕ → E) (hH : Summable (fun j => ‖H j‖ ^ 2))
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    modelCovarianceTrace (fun y => f y + g y) H x =
      modelCovarianceTrace f H x + modelCovarianceTrace g H x := by
  rw [modelCovarianceTrace_eq_bilinearTraceMap H hH (hf.add hg) x,
    modelCovarianceTrace_eq_bilinearTraceMap H hH hf x,
    modelCovarianceTrace_eq_bilinearTraceMap H hH hg x,
    mainInverse_fderiv_fderiv_add hf hg x]
  exact (bilinearTraceMap H hH).map_add _ _

private theorem mainInverse_secondDirectionalDerivative_comp_linear
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (hf : ContDiff ℝ 2 f) (L : E →L[ℝ] F)
    (x v : E) :
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

private theorem mainInverse_modelCovarianceTrace_comp_linear
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (hf : ContDiff ℝ 2 f) (L : E →L[ℝ] F)
    (H : ℕ → E) (x : E) :
    modelCovarianceTrace (fun y => f (L y)) H x =
      modelCovarianceTrace f (fun j => L (H j)) (L x) := by
  unfold modelCovarianceTrace
  apply tsum_congr
  intro j
  exact mainInverse_secondDirectionalDerivative_comp_linear f hf L x (H j)

/-- The OLD-frame inverse trace's covariance Hessian is the sum of the two
actual pure-flux response Hessian traces at loads `(0,e₀)` and `(0,e₁)`. -/
theorem mainInverseObservable_covarianceTrace_eq_two_pureFluxHessians
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (H : ℕ → C(closure (cubeSet (originCube 2 n)), ℝ))
    (hH : Summable (fun j => ‖H j‖ ^ 2))
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    modelCovarianceTrace (mainInverseObservable n ν σ) H x =
      ∑ i : Fin 2, ∑' j : ℕ,
        pureFluxResponseHessianDiagonal
          (measurableSet_cubeSet (originCube 2 n))
          (volume_cubeSet_toReal_pos (originCube 2 n)) ν σ hν hσ
          (0, Pi.single i 1)
          ((ContinuousMap.linearIsometryBoundedOfCompact
            (closure (cubeSet (originCube 2 n))) ℝ ℝ) x)
          ((ContinuousMap.linearIsometryBoundedOfCompact
            (closure (cubeSet (originCube 2 n))) ℝ ℝ) (H j)) := by
  let U := cubeSet (originCube 2 n)
  let K := closure U
  let L : C(K, ℝ) →L[ℝ] ResponseCoefficient U :=
    (ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ).toLinearIsometry.toContinuousLinearMap
  let Hc : ℕ → ResponseCoefficient U := fun j => L (H j)
  let E (i : Fin 2) : ResponseCoefficient U → ℝ := fun k =>
    responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 n))
      (volume_cubeSet_toReal_pos (originCube 2 n)) ν σ hν hσ
      (0, Pi.single i 1) k
  have hE (i : Fin 2) : ContDiff ℝ 2 (E i) := by
    exact (responseFrameEnergyObservable_contDiff
      (measurableSet_cubeSet (originCube 2 n))
      (volume_cubeSet_toReal_pos (originCube 2 n)) ν σ hν hσ
      (0, Pi.single i 1))
  have heq : mainInverseObservable n ν σ =
      fun k => E 0 (L k) + E 1 (L k) := by
    funext k
    rw [mainInverseObservable_eq_twoLoad n ν σ hν hσ k]
    simp only [Fin.sum_univ_two, E, U, K, L,
      LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry]
  have hadd : modelCovarianceTrace (fun k => E 0 (L k) + E 1 (L k)) H x =
      modelCovarianceTrace (fun k => E 0 (L k)) H x +
        modelCovarianceTrace (fun k => E 1 (L k)) H x := by
    simpa only [Function.comp_def] using mainInverse_modelCovarianceTrace_add H hH
      ((hE 0).comp L.contDiff) ((hE 1).comp L.contDiff) x
  have hload (i : Fin 2) :
      modelCovarianceTrace (E i) Hc (L x) =
        ∑' j : ℕ,
          pureFluxResponseHessianDiagonal
            (measurableSet_cubeSet (originCube 2 n))
            (volume_cubeSet_toReal_pos (originCube 2 n)) ν σ hν hσ
            (0, Pi.single i 1)
            (L x) (L (H j)) := by
    simpa only [E, Hc] using
      responseFrameEnergyObservable_covarianceTrace_eq_hessianDiagonal_sum
        (measurableSet_cubeSet (originCube 2 n))
        (volume_cubeSet_toReal_pos (originCube 2 n)) ν σ hν hσ
        (0, Pi.single i 1) Hc (L x)
  have hcomp0 : modelCovarianceTrace (fun k => E 0 (L k)) H x =
      modelCovarianceTrace (E 0) Hc (L x) := by
    exact mainInverse_modelCovarianceTrace_comp_linear
      (E := C(K, ℝ)) (F := ResponseCoefficient U) (E 0) (hE 0) L H x
  have hcomp1 : modelCovarianceTrace (fun k => E 1 (L k)) H x =
      modelCovarianceTrace (E 1) Hc (L x) := by
    exact mainInverse_modelCovarianceTrace_comp_linear
      (E := C(K, ℝ)) (F := ResponseCoefficient U) (E 1) (hE 1) L H x
  rw [heq, hadd, hcomp0, hcomp1, hload 0, hload 1]
  simp only [Fin.sum_univ_two, L, K, U, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry]

end ASDExplicitGamma.Main

end
