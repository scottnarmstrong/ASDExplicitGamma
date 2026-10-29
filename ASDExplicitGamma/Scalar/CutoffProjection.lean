module

public import ASDExplicitGamma.Scalar.ProjectionCharacterization
public import ASDExplicitGamma.Scalar.CutoffPatching

/-! The actual cell solve as a Hilbert affine projection. -/
@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization Response

/-- The weighted projection residual is the actual affine minimizer for an
arbitrary square-integrable cell load. -/
theorem scalarProjectionResidual_eq_affineMinimizer
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (F : HilbertBlockL2 (openCubeSet Q)) :
    scalarProjectionResidual Q ν σ hν hσ k F =
      Homogenization.affineMinimizerMap
        (scalarFrameRealization Q ν σ hν hσ k).correctionSpace.correctionSpace
        (scalarFrameRealization Q ν σ hν hσ k).energyBilin
        (scalarFrameRealization Q ν σ hν hσ k).energyCoercive F := by
  let R := scalarFrameRealization Q ν σ hν hσ k
  let K := R.correctionSpace.correctionSpace
  let B := R.energyBilin
  let z := scalarProjectionResidual Q ν σ hν hσ k F
  let q := Homogenization.affineMinimizerMap K B R.energyCoercive F
  have hFz : F - z ∈ K := by
    simpa [z, K, R] using scalar_projection_removed_mem Q ν σ hν hσ k F
  have hzF : z - F ∈ K := by
    have := K.toSubmodule.neg_mem hFz
    simpa using this
  have hqF : q - F ∈ K := by
    exact Homogenization.sub_affineMinimizerMap_apply_mem K B R.energyCoercive F
  have hqz : q - z ∈ K := by
    have heq : q - z = (q - F) - (z - F) := by abel
    rw [heq]
    exact K.toSubmodule.sub_mem hqF hzF
  have horth := scalar_projection_residual_orthogonal Q ν σ hν hσ k F (q - z) hqz
  have hqeq : q = z + (q - z) := by abel
  have henergy : Homogenization.quadraticEnergy B z ≤
      Homogenization.quadraticEnergy B q := by
    rw [hqeq, Homogenization.quadraticEnergy_add R.energySymm]
    have hfirst : B z (q - z) = 0 := by
      simpa [z, q, B, R] using horth
    rw [hfirst]
    have hnonneg := Homogenization.quadraticEnergy_nonneg R.energyCoercive (q - z)
    nlinarith
  have hmin := Homogenization.eq_affineMinimizerMap_of_quadraticEnergy_le
    K R.energyCoercive R.energySymm F z hzF henergy
  simpa [z, q, K, B, R] using hmin

end ASDExplicitGamma.Scalar
