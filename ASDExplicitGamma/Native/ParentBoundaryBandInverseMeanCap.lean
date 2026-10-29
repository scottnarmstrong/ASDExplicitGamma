module

public import ASDExplicitGamma.Native.ParentBoundaryBandBlockLaw
public import ASDExplicitGamma.Native.ParentBoundaryBandDepthBank
public import ASDExplicitGamma.Native.OldSignedRareTraceIntegral

/-! The actual expected inverse block coefficient on every source cell,
with the complete original local-bank reserve. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The actual lower-right diagonal is dominated by the same depth-zero
inverse maximum in the fixed starting frame. -/
theorem parent_boundary_band_inverse_diagonal_le (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (omega : Cutoff.CutoffSample 2) :
    parentBoundaryBandNormalizedBlock M n height t U false omega 0 0≤
      lemmaVInverseDepthMax U (parentBoundaryBandFrameField M n height t omega) 0 := by
  let a := parentBoundaryBandFrameField M n height t omega
  have hEll := (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet (originCube 2 n))
    M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
    (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t omega))).mono
    (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have he : lemmaVInverseDepthMax U a 0=Book.Ch02.matrixNorm
      (parentBoundaryBandNormalizedBlock M n height t U false omega) := by
    unfold lemmaVInverseDepthMax
    simp only [descendantsAtDepth_zero,Book.Ch02.finsetSupReal,Finset.coe_singleton,Set.image_singleton,csSup_singleton]
    rw [inverse_history_lowerRight U a hEll]
    dsimp only [a,parentBoundaryBandFrameField]
    rw [native_source_band_coarse_matrix_frame M n height t omega hU]
    rfl
  rw [he]
  exact (le_abs_self _).trans (clipped_matrix_entry_abs_le_norm _ 0 0)

end
end ASDExplicitGamma.Native
