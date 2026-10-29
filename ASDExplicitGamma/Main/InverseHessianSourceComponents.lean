module

public import ASDExplicitGamma.Main.InverseHessianCenteredQ3
public import ASDExplicitGamma.Inverse.PureFluxGeneratorSource

/-! The centered inverse covariance trace in its exact source components. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Variational
open scoped BigOperators

/-- The centered q3 inverse-trace covariance Hessian is exactly the sum of
its positive pure source, signed shear feedback, and negative projected
adjoint source terms. -/
theorem mainInverseObservable_covarianceTrace_mainCubeQ3_centered_source_components
    (n : ℤ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (Lscale : {l : ℝ // 0 < l})
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Q := originCube 2 n
    let K := closure (cubeSet Q)
    let toResponse := ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ
    let H (j : ℕ) : ResponseCoefficient (cubeSet Q) :=
      toResponse (pureFluxMainCubeQ3Directions n b Lscale j -
        ContinuousMap.const K
          (pureFluxMainCubeQ3Directions n b Lscale j (pureFluxParentCenter n)))
    let source (i : Fin 2) (j : ℕ) : ℝ :=
      let hU := measurableSet_cubeSet Q
      let hvol := volume_cubeSet_toReal_pos Q
      let P : BlockVec 2 := (0, Pi.single i 1)
      let k := toResponse x
      let S := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
      let C := responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
      let Y := pureFluxResponseGeneratorY hU hvol ν σ hν hσ P k (H j)
      let Z := pureFluxResponseGeneratorZ hU hvol ν σ hν hσ P k (H j)
      ‖Y‖ ^ 2 + 2 * inner ℝ S (C (H j) Y) - ‖Z‖ ^ 2
    (1 / 2 : ℝ) * modelCovarianceTrace (mainInverseObservable n ν σ)
      (fun j => pureFluxMainCubeQ3Directions n b Lscale j -
        ContinuousMap.const _
          (pureFluxMainCubeQ3Directions n b Lscale j (pureFluxParentCenter n))) x =
      ∑ i : Fin 2, ∑' j : ℕ, source i j := by
  dsimp only
  rw [mainInverseObservable_covarianceTrace_mainCubeQ3_centered_eq_twoPureFluxHessians
    n ν σ b hν hσ Lscale x |>.2]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [pureFluxResponseHessianDiagonal_source_identity]

end ASDExplicitGamma.Main

end
