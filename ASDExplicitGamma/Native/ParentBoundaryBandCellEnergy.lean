module

public import ASDExplicitGamma.Native.ParentBoundaryBandCellMoments
public import ASDExplicitGamma.Native.ParentBoundaryBandMatrixMean
public import ASDExplicitGamma.Variational.AdapterAmplitude

/-! Identification of genuine cell-energy moments with the literal
physical finite-band coarse matrix in the fixed starting frame. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- The actual source-cell variational observable is the quadratic form
of the physical band matrix, with sigma_n fixed throughout. -/
theorem parent_boundary_band_cell_energy_eq
    (M : ABKModel 2) (n : ℤ) (height depth : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) depth)
    (P : BlockVec 2) (t : ℝ) (omega : Cutoff.CutoffSample 2) :
    responseFrameEnergyObservable (measurableSet_cubeSet U) (volume_cubeSet_toReal_pos U)
      M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1 P
      (parentBoundaryCellCoefficient hU (nativeSourceBandScalar n height t omega))=
      blockVecDot P (blockMatVecMul (frameMatrix (Annealed.sigmaBar M n)
        (coarseBlockMatrix (cubeSet U)
          (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega))) P) := by
  let k := parentBoundaryCellCoefficient hU (nativeSourceBandScalar n height t omega)
  have heq : responsePlanarCoefficientField M.nu k =ᵐ[volume.restrict (cubeSet U)]
      attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega := by
    filter_upwards [ae_restrict_mem (measurableSet_cubeSet U)] with x hx
    have hxQ := cubeSet_subset_of_mem_descendantsAtDepth hU hx
    change responsePlanarCoefficient M.nu (responseCoefficientExtension k x)=_
    rw [parent_boundary_cell_coefficient_value hU _ hx]
    have hh := native_source_band_coefficient_on_cube M n height t omega x hxQ
    rw [responsePlanarCoefficientField,responseCoefficientExtension_eq _ hxQ,
      ContinuousMap.linearIsometryBoundedOfCompact_apply_apply] at hh
    exact hh
  rw [responseFrameEnergyObservable_eq_frameCoarseQuadratic,
    coarseBlockMatrix_congr_of_ae_eq heq]

end
end ASDExplicitGamma.Native
