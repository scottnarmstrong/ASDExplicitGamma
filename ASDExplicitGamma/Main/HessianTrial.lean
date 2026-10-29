module

public import ASDExplicitGamma.Response.Analytic

/-! The exact physical-coefficient trial-field Hessian step. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Response

/-- The trial-field estimate for the actual coefficient-indexed response,
frozen at its actual coefficient and deterministic positive frame. The
localized DIAG operator still has to replace the global shear for the
quantitative main-generator bound. -/
theorem main_response_hessian_trial_bound
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma) (P : BlockVec 2)
    (k H : ResponseCoefficient U) :
    let D := responseFrameEnergyData hU hvol nu sigma hnu hsigma k
    let V := responseFrameEnergyVariationSpace hU hvol nu sigma hnu hsigma k
    let C : ResponseCoefficient U →L[ℝ] (EnergyCarrier D →L[ℝ] EnergyCarrier D) :=
      responseFrameEnergyShearFamily hU hvol nu sigma hnu hsigma k
    let S : EnergyCarrier D := responseFrameEnergyBaseMinimizer hU hvol nu sigma hnu hsigma k P
    ∀ Y : V.toSubmodule,
      (1 / 2 : ℝ) * fderiv ℝ (fun z => fderiv ℝ
        (responseFrameEnergyObservable hU hvol nu sigma hnu hsigma P) z H) k H ≤
      ‖C H S + (Y : EnergyCarrier D)‖ ^ 2 +
        2 * inner ℝ S (C H (Y : EnergyCarrier D)) := by
  intro D V C S Y
  have hnil := responseFrameEnergyShearFamily_pairwise_nilpotent hU hvol nu sigma hnu hsigma k
  have horth : ∀ Z : V.toSubmodule, inner ℝ S (Z : EnergyCarrier D) = 0 := by
    intro Z
    exact responseEnergyMinimizer_orthogonal
      ((responseFrameMuOperatorSystemData hU hvol nu sigma hnu hsigma k).toMuHilbertRealization) P Z
  have htrial := linearShearMinimum_trial_bound_zero V C S hnil horth H Y
  rw [linearShearMinimum_second_fderiv_zero V C S hnil horth H H] at htrial
  rw [responseFrameEnergyObservable_hessian]
  exact htrial

end ASDExplicitGamma.Main
