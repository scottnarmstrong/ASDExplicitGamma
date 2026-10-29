module

public import ASDExplicitGamma.Native.ParentBoundaryBandCellEnergy

/-! Actual finite Gaussian moments of every framed source-cell matrix entry,
obtained from the true variational energies by exact polarization. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse
open scoped ENNReal
noncomputable section

/-- Every actual framed coarse entry on a source cell has all finite
moments. No entry or response-norm estimate is supplied as a premise. -/
theorem parent_boundary_band_cell_entry_memLp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1≤height) (depth : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) depth)
    (alpha beta : BlockCoord 2) (t p : ℝ) (hp : 2≤p) :
    MemLp (fun omega : Cutoff.CutoffSample 2 => blockMatEntry
      (frameMatrix (Annealed.sigmaBar M n) (coarseBlockMatrix (cubeSet U)
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega))) alpha beta)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure := by
  let E := fun (P : BlockVec 2) (omega : Cutoff.CutoffSample 2) =>
    responseFrameEnergyObservable (measurableSet_cubeSet U) (volume_cubeSet_toReal_pos U)
      M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1 P
      (parentBoundaryCellCoefficient hU (nativeSourceBandScalar n height t omega))
  have hm (P : BlockVec 2) : MemLp (E P) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure :=
    parent_boundary_band_cell_energy_memLp M h hM n height hheight depth U hU P t p hp
  have hh := (((hm (blockBasis alpha+blockBasis beta)).sub (hm (blockBasis alpha))).sub
    (hm (blockBasis beta))).const_mul (1/2:ℝ)
  refine (memLp_congr_ae ?_).mp hh
  filter_upwards [] with omega
  let A := frameMatrix (Annealed.sigmaBar M n) (coarseBlockMatrix (cubeSet U)
    (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega))
  have hs : IsSymmetricBlockMat A := by
    have hc := coarseBlockMatrix_symmetric (cubeSet U)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
        (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t omega)))
    rw [native_source_band_coarse_matrix_frame M n height t omega hU] at hc
    exact hc
  change (1/2:ℝ)*(E (blockBasis alpha+blockBasis beta) omega-E (blockBasis alpha) omega-
    E (blockBasis beta) omega)=blockMatEntry A alpha beta
  have he (P : BlockVec 2) : E P omega=blockVecDot P (blockMatVecMul A P) :=
    parent_boundary_band_cell_energy_eq M n height depth U hU P t omega
  rw [he,he,he,blockBasis_sum_pairing,blockBasis_pairing,blockBasis_pairing,hs beta alpha]
  ring

end
end ASDExplicitGamma.Native
