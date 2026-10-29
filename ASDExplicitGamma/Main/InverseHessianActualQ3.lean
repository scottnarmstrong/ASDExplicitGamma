module

public import ASDExplicitGamma.Main.InverseHessianIdentity
public import ASDExplicitGamma.Inverse.PureFluxGeneratorActualQ3

/-! The fixed-frame inverse-trace Hessian identity for the actual q3 heat directions. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse

/-- The OLD-frame inverse trace's covariance Hessian for the actual main-cube
q3 directions is the sum of its two pure-flux response Hessian traces. The
directional square summability is derived from the q3 heat realization. -/
theorem mainInverseObservable_covarianceTrace_mainCubeQ3_eq_two_pureFluxHessians
    (n : ℤ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    modelCovarianceTrace (mainInverseObservable n ν σ)
        (pureFluxMainCubeQ3Directions n b L) x =
      ∑ i : Fin 2, ∑' j : ℕ,
        pureFluxResponseHessianDiagonal
          (measurableSet_cubeSet (originCube 2 n))
          (volume_cubeSet_toReal_pos (originCube 2 n)) ν σ hν hσ
          (0, Pi.single i 1)
          ((ContinuousMap.linearIsometryBoundedOfCompact
            (closure (cubeSet (originCube 2 n))) ℝ ℝ) x)
          ((ContinuousMap.linearIsometryBoundedOfCompact
            (closure (cubeSet (originCube 2 n))) ℝ ℝ)
            (pureFluxMainCubeQ3Directions n b L j)) := by
  let H := pureFluxMainCubeQ3Directions n b L
  let v := mainCubeQ3Directions n b L
  let T := mainCubeH3Value n b L
  have hA := mainCubeQ3Directions_summable n b L
  have hH : Summable (fun j => ‖T (v j)‖ ^ 2) :=
    @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
      C(closure (cubeSet (originCube 2 n)), ℝ)
      inferInstance (mainCubeH3InnerProductSpace n b L).toNormedSpace
      inferInstance inferInstance v hA T
  have hH' : Summable (fun j => ‖H j‖ ^ 2) := by
    simpa only [H, pureFluxMainCubeQ3Directions, v, T] using hH
  simpa only [H, pureFluxMainCubeQ3Directions] using
    mainInverseObservable_covarianceTrace_eq_two_pureFluxHessians
      n ν σ hν hσ H hH' x

end ASDExplicitGamma.Main
