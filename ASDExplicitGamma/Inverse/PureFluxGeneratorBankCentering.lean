module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLaw
public import ASDExplicitGamma.Inverse.PureFluxGeneratorCentering

/-! Exact fixed-parent centering of the physical inverse-trace covariance. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization ASDExplicitGamma.Gaussian
noncomputable section

theorem pureFlux_bank_covarianceTrace_centered (k : ℤ) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ)
    (H : ℕ → C(closure (cubeSet (originCube 2 k)), ℝ))
    (x : C(closure (cubeSet (originCube 2 k)), ℝ))
    (center : closure (cubeSet (originCube 2 k))) :
    modelCovarianceTrace (bankInverseTraceObservable k ν σ hν hσ)
      (fun j => H j - ContinuousMap.const _ (H j center)) x =
      modelCovarianceTrace (bankInverseTraceObservable k ν σ hν hσ) H x := by
  apply pureFlux_modelCovarianceTrace_sub_gauges _
    (bank_inverse_trace_observable_C2 k ν σ hν hσ).1
  intro j y t
  have heq : t • ContinuousMap.const (closure (cubeSet (originCube 2 k))) (H j center) =
      ContinuousMap.const _ (t*(H j center)) := by
    ext z
    rfl
  rw [heq]
  exact bank_inverse_trace_observable_add_const k ν σ hν hσ y _

/-- Removing the value at one fixed parent point is a continuous linear map. -/
def pureFluxCoefficientCentering {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (center : K) : C(K, ℝ) →L[ℝ] C(K, ℝ) :=
  ContinuousLinearMap.id ℝ C(K, ℝ) -
    (ContinuousLinearMap.const ℝ K : ℝ →L[ℝ] C(K, ℝ)).comp (ContinuousMap.evalCLM ℝ center)

@[simp] theorem pureFluxCoefficientCentering_apply {K : Type*} [TopologicalSpace K]
    [CompactSpace K] (center : K) (f : C(K, ℝ)) :
    pureFluxCoefficientCentering center f = f-ContinuousMap.const K (f center) := by
  ext y
  simp [pureFluxCoefficientCentering]

theorem pureFlux_centered_directions_summable {K : Type*} [TopologicalSpace K]
    [CompactSpace K] (center : K) (H : ℕ → C(K, ℝ))
    (hH : Summable (fun j => ‖H j‖^2)) :
    Summable (fun j => ‖H j-ContinuousMap.const K (H j center)‖^2) := by
  simpa only [pureFluxCoefficientCentering_apply] using
    summable_sq_bounded_image H hH (pureFluxCoefficientCentering center)

end
end ASDExplicitGamma.Inverse
