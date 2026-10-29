module

public import ASDExplicitGamma.Native.OldSignedAffineExpectation

/-! Stationary scalar coefficients for the exact signed OLD affine term. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- Whole-sample translation makes the scalar block mean depend only on
the physical cell scale, keeping the completed starting frame fixed. -/
theorem old_signed_block_mean_eq_origin (M : ABKModel 2) (n : ℤ) (t : ℝ)
    (U : TriadicCube 2) (plus : Bool) :
    parentBoundaryBandBlockMean M n 1 t U plus=
      parentBoundaryBandBlockMean M n 1 t (originCube 2 U.scale) plus := by
  have he (ω : Cutoff.CutoffSample 2) : parentBoundaryBandNormalizedBlock M n 1 t U plus ω 0 0=
      parentBoundaryBandNormalizedBlock M n 1 t (originCube 2 U.scale) plus
        (Cutoff.translateCutoffSample (triadicCubeShift U) ω) 0 0 := by
    unfold parentBoundaryBandNormalizedBlock
    rw [parent_boundary_band_coarse_cell_translate]
  unfold parentBoundaryBandBlockMean
  simp_rw [he]
  exact integral_cutoffSample_vadd M (triadicCubeShift U) (fun ω =>
    parentBoundaryBandNormalizedBlock M n 1 t (originCube 2 U.scale) plus ω 0 0)

/-- Every cell in the comparison tiling has the same literal signed scalar
coefficient, including at smaller gamma. -/
theorem old_signed_block_mean_eq_depth (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (plus : Bool) :
    parentBoundaryBandBlockMean M n 1 t U plus=
      parentBoundaryBandBlockMean M n 1 t (originCube 2 (n-(r:ℤ))) plus := by
  rw [old_signed_block_mean_eq_origin,scale_eq_sub_of_mem_descendantsAtDepth hU]
  rfl

/-- Exact scalar form of the integrated signed affine contribution. Both
block deviations keep their signs; only the deterministic flat means are
averaged over the full comparison tiling. -/
theorem old_signed_affine_scalar_expectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (r : ℕ) (t b : ℝ) (L : {l : ℝ // 0<l}) :
    (∫ ω,oldSignedFlatAffineContribution (originCube 2 n) r
      (oldSignedPartialFrameField M n 1 t ω) b L ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      (parentBoundaryBandBlockMean M n 1 t (originCube 2 (n-(r:ℤ))) false-1)*
        descendantsAverage (originCube 2 n) r (fun U => oldSignedFlatMeanSize (originCube 2 n) U b L true^2)+
      (parentBoundaryBandBlockMean M n 1 t (originCube 2 (n-(r:ℤ))) true-1)*
        descendantsAverage (originCube 2 n) r (fun U => oldSignedFlatMeanSize (originCube 2 n) U b L false^2) := by
  rw [(old_signed_affine_expectation M h hM n r t b L).2]
  rw [←descendantsAverage_mul_left,←descendantsAverage_mul_left,←descendantsAverage_add]
  unfold descendantsAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [old_signed_block_mean_eq_depth M n r U hU t false,
    old_signed_block_mean_eq_depth M n r U hU t true]

end
end ASDExplicitGamma.Native
