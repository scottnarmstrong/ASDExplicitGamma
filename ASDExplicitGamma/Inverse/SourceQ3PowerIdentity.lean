module

public import ASDExplicitGamma.Inverse.SourceQ3CovarianceLaw

/-! Exact p20 covariance-to-power-generator identity in the canonical
physical q3 shell directions, before any coefficient estimate. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
noncomputable section

theorem source_q3_covariance_power_identity
    (n : ℤ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (L : {l : ℝ // 0 < l})
    (x : C(closure (cubeSet (originCube 2 n)),ℝ)) :
    (1/2:ℝ)*modelCovarianceTrace (fun y => modelTraceObservable n ν σ y^(20:ℝ))
      (pureFluxMainCubeQ3Directions n b L) x =
      modelPowerHeatGenerator (modelTraceObservable n ν σ) (pureFluxMainCubeQ3Directions n b L) 20 x := by
  exact @modelCovarianceTrace_rpow (MainCubeH3 n b L)
    (C(closure (cubeSet (originCube 2 n)),ℝ))
    inferInstance (mainCubeH3InnerProductSpace n b L) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (mainCubeQ3Directions n b L) (mainCubeQ3Directions_summable n b L)
    (mainCubeH3Value n b L) (modelTraceObservable n ν σ)
    (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n ν σ hν hσ)
    (modelTraceObservable_nonneg n ν σ hν hσ) 20 (by norm_num : (2:ℝ)≤20) x

end
end ASDExplicitGamma.Inverse
