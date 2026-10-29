module

public import ASDExplicitGamma.Native.ParentBoundaryBandDirectionalHistory

/-! The actual local response restriction consumes the source-law directional budget. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Algsuperdiff.Section3
noncomputable section

/-- The local directional proxy used by the actual flat-cell construction is
identical to the proxy of the parent display field on that cell. -/
theorem parent_boundary_band_local_proxy_eq (M : ABKModel 2) (n : ℤ) (height : ℕ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (e : Vec 2) :
    oldSignedDirectionalProxy U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
      (oldSignedCellCoefficient (originCube 2 n) U
        (openCubeSet_subset_of_mem_descendantsAtDepth hU) (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω)))) e=
      oldSignedDirectionalProxy U (parentBoundaryBandFrameField M n height t ω) e := by
  let k := pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω)
  have hσ := (Annealed.sigmaBar_characterization M n).1
  apply old_signed_directional_proxy_congr U _ _
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U)
      M.nu (Annealed.sigmaBar M n) M.nu_pos hσ _)
    ((responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet (originCube 2 n))
      M.nu (Annealed.sigmaBar M n) M.nu_pos hσ k).mono (measurableSet_openCubeSet U)
      (openCubeSet_subset_of_mem_descendantsAtDepth hU))
  exact old_signed_cell_frame_coefficient_ae (originCube 2 n) U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) M.nu (Annealed.sigmaBar M n) k

end
end ASDExplicitGamma.Native
