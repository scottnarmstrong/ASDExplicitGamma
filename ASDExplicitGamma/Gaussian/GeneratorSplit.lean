module

public import ASDExplicitGamma.Gaussian.BackwardHeat
public import ASDExplicitGamma.Gaussian.ObservedCovariance

/-! # Center, mixed and remainder generators with exact cancellation -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

section
variable {n : ℕ} {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The exact canceled generator in (8.19). The mixed term contains the actual center/remainder
covariance and is never dropped by an independence assertion. -/
noncomputable def cancelledGenerator (H : ℕ → E) (P : E →L[ℝ] X)
    (L : E →L[ℝ] (Fin n → ℝ)) (I : (Fin n → ℝ) →L[ℝ] X)
    (Φ : X → ℝ) (θ : ℝ) (x : X) : ℝ :=
  -θ * centerGenerator H L I (fderiv ℝ (fderiv ℝ Φ) x) +
    mixedGenerator H L I (P - I.comp L) (fderiv ℝ (fderiv ℝ Φ) x) +
    (1 / 2 : ℝ) * ∑' j, fderiv ℝ (fderiv ℝ Φ) x
      ((P - I.comp L) (H j)) ((P - I.comp L) (H j))

/-- The center generator, with the actual field Hessian and its full physical center matrix. -/
theorem response_generator_split {H : ℕ → E}
    (hH : Summable (fun j => ‖H j‖ ^ 2))
    (P : E →L[ℝ] X) (L : E →L[ℝ] (Fin n → ℝ)) (I : (Fin n → ℝ) →L[ℝ] X)
    {Φ : X → ℝ} (hΦ : ContDiff ℝ 2 Φ) (x : X) :
    (1 / 2 : ℝ) * modelCovarianceTrace Φ (fun j => P (H j)) x =
      centerGenerator H L I (fderiv ℝ (fderiv ℝ Φ) x) +
      mixedGenerator H L I (P - I.comp L) (fderiv ℝ (fderiv ℝ Φ) x) +
      (1 / 2 : ℝ) * ∑' j, fderiv ℝ (fderiv ℝ Φ) x
        ((P - I.comp L) (H j)) ((P - I.comp L) (H j)) := by
  rw [modelCovarianceTrace_eq_bilinearTraceMap _ (summable_sq_norm_map hH P) hΦ]
  exact generator_split hH P L I (fderiv ℝ (fderiv ℝ Φ) x)
    ((hΦ.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq)

/-- Subtracting the independent auxiliary generator leaves exactly −θ times the full center
generator, plus the mixed and remainder generators. -/
theorem generator_cancellation {H : ℕ → E}
    (hH : Summable (fun j => ‖H j‖ ^ 2))
    (P : E →L[ℝ] X) (L : E →L[ℝ] (Fin n → ℝ)) (I : (Fin n → ℝ) →L[ℝ] X)
    {Φ : X → ℝ} (hΦ : ContDiff ℝ 2 Φ) (θ : ℝ) :
    backwardGenerator Φ (fun j => P (H j)) (fun j => I (L (H j))) θ =
      cancelledGenerator H P L I Φ θ := by
  funext x
  have hsplit := response_generator_split hH P L I hΦ x
  have hcenter : (1 / 2 : ℝ) * modelCovarianceTrace Φ (fun j => I (L (H j))) x =
      centerGenerator H L I (fderiv ℝ (fderiv ℝ Φ) x) := by
    have heq : modelCovarianceTrace Φ (fun j => I (L (H j))) x =
        ∑' j, fderiv ℝ (fderiv ℝ Φ) x (I (L (H j))) (I (L (H j))) := by
      apply tsum_congr
      intro j
      exact second_fderiv_eq hΦ _ _ _
    rw [heq]
    exact center_generator_eq hH L I _
  unfold backwardGenerator cancelledGenerator
  have haux : modelCovarianceTrace Φ (fun j => I (L (H j))) x =
      2 * centerGenerator H L I (fderiv ℝ (fderiv ℝ Φ) x) := by linarith only [hcenter]
  rw [hsplit, haux]
  ring

end

/-- Physical center covariance is the auxiliary Gaussian expectation in (8.18). -/
theorem centerCovariance_eq_integral {V E : Type*} {n : ℕ}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (L : E →L[ℝ] (Fin n → ℝ)) (i l : Fin n) :
    centerCovariance (fun j => T (v j)) L i l =
      ∫ ω, L (gaussianSeriesLimitE hA T ω) i * L (gaussianSeriesLimitE hA T ω) l
        ∂standardGaussianInfinitePi :=
  (integral_observations_mul hA T ((ContinuousLinearMap.proj i).comp L)
    ((ContinuousLinearMap.proj l).comp L)).symm

/-- The exact cancellation, with C¹ endpoints and the exact cancellation inside the actual/auxiliary
expectation. No center/remainder independence is needed. -/
theorem c1On_cancelledBackwardAverage {V E X : Type*} {n : ℕ}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (P : E →L[ℝ] X) (L : E →L[ℝ] (Fin n → ℝ)) (I : (Fin n → ℝ) →L[ℝ] X)
    (ν : Measure X) [IsFiniteMeasure ν]
    (hν : ∀ d : ℕ, Integrable (fun x : X => (1 + ‖x‖) ^ d) ν)
    {Φ : X → ℝ} (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) {θ : ℝ} (hθ : 0 < θ) :
    let F := backwardAverage hA (P.comp T) hA ((I.comp L).comp T) ν Φ θ
    let D := backwardAverage hA (P.comp T) hA ((I.comp L).comp T) ν
      (cancelledGenerator (fun j => T (v j)) P L I Φ θ) θ
    ContinuousOn F (Icc 0 1) ∧ ContinuousOn D (Icc 0 1) ∧
    (∀ t ∈ Ioo 0 1, HasDerivAt F (D t) t) ∧
    HasDerivWithinAt F (D 0) (Icc 0 1) 0 ∧ HasDerivWithinAt F (D 1) (Icc 0 1) 1 := by
  have h := c1On_backwardAverage hA (P.comp T) hA ((I.comp L).comp T) ν hν hΦ hθ
  have heq := generator_cancellation (summable_sq_norm_gaussianDirections hA T) P L I hΦ.1 θ
  simpa only [ContinuousLinearMap.comp_apply, heq] using h

end ASDExplicitGamma.Gaussian
