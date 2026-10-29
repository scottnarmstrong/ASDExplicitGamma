module

public import ASDExplicitGamma.Native.HeatVHEATBracketMeanDerivative

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3

noncomputable section

/-- The pointwise parent-source identity, assembled as an equality of
continuous linear functionals on white noise. -/
theorem nativeHeatQ3RefinedCarrierParentMeanDerivativeCLM_eq_remainderObservations
    (M : ABKModel 2) (h : ℝ)
    (m : ℤ) (d : Fin 9) (σ : ℝ) (hσ : 0 < σ)
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    (((fderiv ℝ (nativeHeatQ3RefinedCarrierMeanTrace M m σ hσ) x).comp
      (nativeHeatQ3RefinedCarrierRemainderMap m)).comp
      (nativeHeatQ3RefinedCarrierParentRestrict m)).comp
      (nativeHeatQ3RefinedCarrierParentSource' M h m d) =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ •
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          nativeHeatQ3RefinedCarrierChildRemainderMeanObservation
            M h m d σ x i := by
  classical
  let L : WhiteNoise →L[ℝ] ℝ :=
    (((fderiv ℝ (nativeHeatQ3RefinedCarrierMeanTrace M m σ hσ) x).comp
      (nativeHeatQ3RefinedCarrierRemainderMap m)).comp
      (nativeHeatQ3RefinedCarrierParentRestrict m)).comp
      (nativeHeatQ3RefinedCarrierParentSource' M h m d)
  have hpoint (u : WhiteNoise) : L u =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
        nativeHeatQ3RefinedCarrierChildRemainderMeanObservation
          M h m d σ x i u := by
    change fderiv ℝ (nativeHeatQ3RefinedCarrierMeanTrace M m σ hσ) x
        (nativeHeatQ3RefinedCarrierRemainderMap m
          (nativeHeatQ3RefinedCarrierParentRestrict m
            (nativeHeatQ3RefinedCarrierParentSource' M h m d u))) =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          nativeHeatQ3RefinedCarrierChildRemainderMeanObservation
            M h m d σ x i u
    exact nativeHeatQ3RefinedCarrierParentMeanDerivative_eq_remainderObservations
      M h m d σ hσ x u
  have hsum : L =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ •
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          nativeHeatQ3RefinedCarrierChildRemainderMeanObservation
            M h m d σ x i := by
    ext u
    simp only [smul_apply, sum_apply, smul_eq_mul]
    exact hpoint u
  calc
    _ = L := rfl
    _ = _ := hsum
    _ = _ := rfl

end

end ASDExplicitGamma.Native
