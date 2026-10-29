module

public import ASDExplicitGamma.Main.InverseHessianActualQ3
public import ASDExplicitGamma.Main.InverseObservableGauge
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankCentering
public import ASDExplicitGamma.Inverse.PureFluxGeneratorDirectionBridge

/-! The actual inverse-trace covariance Hessian is unchanged by centering
each constant-skew q3 direction. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Variational
open scoped BigOperators

/-- Centering every coefficient direction at one point leaves the actual
fixed-frame inverse covariance trace unchanged, and its centered trace is
the sum of the corresponding two-load response Hessians. -/
theorem mainInverseObservable_covarianceTrace_centered_eq_twoPureFluxHessians
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (H : ℕ → C(closure (cubeSet (originCube 2 n)), ℝ))
    (hH : Summable (fun j => ‖H j‖ ^ 2))
    (center : closure (cubeSet (originCube 2 n)))
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    modelCovarianceTrace (mainInverseObservable n ν σ)
        (fun j => H j - ContinuousMap.const _ (H j center)) x =
      modelCovarianceTrace (mainInverseObservable n ν σ) H x ∧
    modelCovarianceTrace (mainInverseObservable n ν σ)
        (fun j => H j - ContinuousMap.const _ (H j center)) x =
      ∑ i : Fin 2, ∑' j : ℕ,
        pureFluxResponseHessianDiagonal
          (measurableSet_cubeSet (originCube 2 n))
          (volume_cubeSet_toReal_pos (originCube 2 n)) ν σ hν hσ
          (0, Pi.single i 1)
          ((ContinuousMap.linearIsometryBoundedOfCompact
            (closure (cubeSet (originCube 2 n))) ℝ ℝ) x)
          ((ContinuousMap.linearIsometryBoundedOfCompact
            (closure (cubeSet (originCube 2 n))) ℝ ℝ)
            (H j - ContinuousMap.const _ (H j center))) := by
  have hC2 : ContDiff ℝ 2 (mainInverseObservable n ν σ) := by
    let K := closure (cubeSet (originCube 2 n))
    let L : C(K, ℝ) →L[ℝ] ResponseCoefficient (cubeSet (originCube 2 n)) :=
      (ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ).toLinearIsometry.toContinuousLinearMap
    let E (i : Fin 2) : ResponseCoefficient (cubeSet (originCube 2 n)) → ℝ := fun k =>
      responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 n))
        (volume_cubeSet_toReal_pos (originCube 2 n)) ν σ hν hσ (0, Pi.single i 1) k
    have hE (i : Fin 2) : ContDiff ℝ 2 (E i) := by
      exact responseFrameEnergyObservable_contDiff
        (measurableSet_cubeSet (originCube 2 n))
        (volume_cubeSet_toReal_pos (originCube 2 n)) ν σ hν hσ (0, Pi.single i 1)
    have heq : mainInverseObservable n ν σ = fun k => E 0 (L k) + E 1 (L k) := by
      funext k
      rw [mainInverseObservable_eq_twoLoad n ν σ hν hσ k]
      simp only [Fin.sum_univ_two, E, L, K,
        LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometryEquiv.coe_toLinearIsometry]
    rw [heq]
    exact ((hE 0).comp L.contDiff).add ((hE 1).comp L.contDiff)
  have hinv (j : ℕ) (y : C(closure (cubeSet (originCube 2 n)), ℝ)) (t : ℝ) :
      mainInverseObservable n ν σ
          (y + t • ContinuousMap.const _ (H j center)) =
        mainInverseObservable n ν σ y := by
    have hconst : t • ContinuousMap.const
        (closure (cubeSet (originCube 2 n))) (H j center) =
        ContinuousMap.const _ (t * H j center) := by
      ext z
      simp
    rw [hconst]
    exact mainInverseObservable_add_const n ν σ (t * H j center) hν y
  have hcenter := pureFlux_modelCovarianceTrace_sub_gauges
    (mainInverseObservable n ν σ) hC2 H
    (fun j => ContinuousMap.const (closure (cubeSet (originCube 2 n))) (H j center))
    hinv x
  have hHcenter : Summable (fun j =>
      ‖H j - ContinuousMap.const (closure (cubeSet (originCube 2 n))) (H j center)‖ ^ 2) :=
    pureFlux_centered_directions_summable center H hH
  refine ⟨hcenter, ?_⟩
  exact mainInverseObservable_covarianceTrace_eq_two_pureFluxHessians
      n ν σ hν hσ (fun j => H j - ContinuousMap.const _ (H j center)) hHcenter x

/-- The actual q3 heat directions can be centered at the parent center before
applying the inverse-trace Hessian adapter. -/
theorem mainInverseObservable_covarianceTrace_mainCubeQ3_centered_eq_twoPureFluxHessians
    (n : ℤ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    modelCovarianceTrace (mainInverseObservable n ν σ)
        (fun j => pureFluxMainCubeQ3Directions n b L j -
          ContinuousMap.const _
            (pureFluxMainCubeQ3Directions n b L j (pureFluxParentCenter n))) x =
      modelCovarianceTrace (mainInverseObservable n ν σ)
        (pureFluxMainCubeQ3Directions n b L) x ∧
    modelCovarianceTrace (mainInverseObservable n ν σ)
        (fun j => pureFluxMainCubeQ3Directions n b L j -
          ContinuousMap.const _
            (pureFluxMainCubeQ3Directions n b L j (pureFluxParentCenter n))) x =
      ∑ i : Fin 2, ∑' j : ℕ,
        pureFluxResponseHessianDiagonal
          (measurableSet_cubeSet (originCube 2 n))
          (volume_cubeSet_toReal_pos (originCube 2 n)) ν σ hν hσ
          (0, Pi.single i 1)
          ((ContinuousMap.linearIsometryBoundedOfCompact
            (closure (cubeSet (originCube 2 n))) ℝ ℝ) x)
          ((ContinuousMap.linearIsometryBoundedOfCompact
            (closure (cubeSet (originCube 2 n))) ℝ ℝ)
            (pureFluxMainCubeQ3Directions n b L j -
              ContinuousMap.const _
                (pureFluxMainCubeQ3Directions n b L j (pureFluxParentCenter n)))) := by
  let H := pureFluxMainCubeQ3Directions n b L
  have hH : Summable (fun j => ‖H j‖ ^ 2) := by
    have hA := mainCubeQ3Directions_summable n b L
    exact @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
      C(closure (cubeSet (originCube 2 n)), ℝ)
      inferInstance (mainCubeH3InnerProductSpace n b L).toNormedSpace
      inferInstance inferInstance (mainCubeQ3Directions n b L) hA
      (mainCubeH3Value n b L)
  have hbase := mainInverseObservable_covarianceTrace_centered_eq_twoPureFluxHessians
    n ν σ hν hσ H hH (pureFluxParentCenter n) x
  simpa only [H] using hbase

end ASDExplicitGamma.Main

end
