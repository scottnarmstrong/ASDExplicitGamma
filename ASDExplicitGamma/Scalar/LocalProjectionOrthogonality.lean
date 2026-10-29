module

public import ASDExplicitGamma.Scalar.ProjectionFields

/-! Restriction of source energy orthogonality to each genuine cell variation. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory

/-- Every source variation on a subcell can be tested against the actual global weighted residual. -/
theorem scalar_residual_local_orthogonal (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (openCubeSet Q))
    (F : HilbertBlockL2 (openCubeSet Q)) (Y : Vec 2 → BlockVec 2)
    (hY : ScalarVariation (openCubeSet R) Y) :
    volumeAverage (openCubeSet R) (fun x => blockVecDot (Y x)
      (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ k) x)
        (scalarResidualField Q ν σ hν hσ k F x)))=0 := by
  have hg := scalar_residual_field_orthogonal Q ν σ hν hσ k F ((openCubeSet R).indicator Y)
    (scalar_variation_zero_extension (isOpen_openCubeSet R) (isOpen_openCubeSet Q) hRQ hY)
  have he : (fun x => blockVecDot (((openCubeSet R).indicator Y) x)
      (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ k) x)
        (scalarResidualField Q ν σ hν hσ k F x)))=
      (openCubeSet R).indicator (fun x => blockVecDot (Y x)
        (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ k) x)
          (scalarResidualField Q ν σ hν hσ k F x))) := by
    funext x
    by_cases hx : x ∈ openCubeSet R <;> simp [hx,blockVecDot,vecDot]
  unfold volumeAverage at hg ⊢
  have hv : (volume (openCubeSet Q)).toReal≠0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  have hi := (mul_eq_zero.mp hg).resolve_left (inv_ne_zero hv)
  rw [he,integral_indicator (measurableSet_openCubeSet R),
    Measure.restrict_restrict (measurableSet_openCubeSet R),Set.inter_eq_left.mpr hRQ] at hi
  rw [hi,mul_zero]

end ASDExplicitGamma.Scalar
