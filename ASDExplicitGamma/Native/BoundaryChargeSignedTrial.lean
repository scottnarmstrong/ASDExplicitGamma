module

public import ASDExplicitGamma.Main.HessianTrial

/-! The signed variational step for the boundary-fixed OLD source. The
nilpotent shear is cancelled before estimating the remaining feedback. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization ASDExplicitGamma.Response
noncomputable section

/-- A candidate residual gives a signed trial whenever subtracting the
actual sheared minimizer is an admissible variation. Nilpotence cancels
the double shear exactly; no absolute value is applied to the feedback. -/
theorem native_boundary_signed_response_trial
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma) (P : BlockVec 2)
    (k H : ResponseCoefficient U) :
    let D := responseFrameEnergyData hU hvol nu sigma hnu hsigma k
    let V := responseFrameEnergyVariationSpace hU hvol nu sigma hnu hsigma k
    let C : ResponseCoefficient U →L[ℝ] (EnergyCarrier D →L[ℝ] EnergyCarrier D) :=
      responseFrameEnergyShearFamily hU hvol nu sigma hnu hsigma k
    let S : EnergyCarrier D := responseFrameEnergyBaseMinimizer hU hvol nu sigma hnu hsigma k P
    ∀ R : EnergyCarrier D, R-C H S ∈ V.toSubmodule →
      (1/2:ℝ)*fderiv ℝ (fun z => fderiv ℝ
        (responseFrameEnergyObservable hU hvol nu sigma hnu hsigma P) z H) k H ≤
        ‖R‖^2+2*inner ℝ S (C H R) := by
  intro D V C S R hR
  let Y : V.toSubmodule := ⟨R-C H S,hR⟩
  have hh := Main.main_response_hessian_trial_bound hU hvol nu sigma hnu hsigma P k H Y
  have hnil : C H (C H S)=0 := by
    have hn : (C H).comp (C H)=0 :=
      responseFrameEnergyShearFamily_pairwise_nilpotent hU hvol nu sigma hnu hsigma k H H
    change ((C H).comp (C H)) S=0
    rw [hn]
    rfl
  have hres : C H S+(Y:EnergyCarrier D)=R := by
    change C H S+(R-C H S)=R
    abel
  have hfeedback : C H (Y:EnergyCarrier D)=C H R := by
    change C H (R-C H S)=C H R
    rw [map_sub,hnil,sub_zero]
  change _ ≤ ‖C H S+(Y:EnergyCarrier D)‖^2+2*inner ℝ S (C H (Y:EnergyCarrier D)) at hh
  simpa only [hres,hfeedback] using hh

end
end ASDExplicitGamma.Native
