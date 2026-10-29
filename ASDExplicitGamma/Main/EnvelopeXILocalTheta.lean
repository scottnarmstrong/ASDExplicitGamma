module

public import ASDExplicitGamma.Inverse.MixedBridgeConclusion

/-! The exact root weighted-Theta row and the local depth-five OLD-Theta row
for MA-ENVELOPE-XI and the directional covariance consumer. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic

/-- On each depth-five source cell, the actual local OLD-Theta variable is
integrable under the unchanged cutoff law and its expectation is bounded by
the exact shifted `xi5` path. This is the local expectation helper; the comparison with the explicit
`mainChi` is supplied separately. -/
theorem main_envelope_xi_local_depth_five_row
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    ∀ U : TriadicCube 2, U ∈ descendantsAtDepth (originCube 2 m) 5 →
      Integrable (fun ω => mixedOldTheta M m U t ω) μ ∧
      (∫ ω, mixedOldTheta M m U t ω ∂μ) ≤
        mixedBridgeLocalXi5 M h m t := by
  exact mixed_bridge_local_old_theta_local_xi5
    M h hM hγ N hpast m hm t ht

end ASDExplicitGamma.Main
