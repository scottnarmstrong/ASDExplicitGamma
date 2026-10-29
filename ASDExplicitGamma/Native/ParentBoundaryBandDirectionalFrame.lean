module

public import ASDExplicitGamma.Native.ParentBoundaryBandHalfTrace
public import ASDExplicitGamma.Native.ParentBoundaryBandDepthBank
public import ASDExplicitGamma.Native.OldSignedSourceCellFrame

/-! The actual paired directional matrix on each simultaneous-band cell,
with one fixed starting frame on the entire descendant tiling. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Algsuperdiff.Section3
noncomputable section

/-- The physical trace sequence on a source-cell descendant tiling. -/
def parentBoundaryBandCellTrace (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (U : TriadicCube 2) (j : ℕ) (omega : Cutoff.CutoffSample 2) : ℝ :=
  descendantsAverage U j (fun V => traceDefect (cubeSet V)
    (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
    (Annealed.sigmaBar M n))

/-- Every physical directional matrix uses sigma_n on every descendant. -/
theorem parent_boundary_band_directional_matrix
    (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (omega : Cutoff.CutoffSample 2) (j : ℕ) :
    oldSignedPairedDepthMatrix U j (parentBoundaryBandFrameField M n height t omega)=
      descendantsAverageMat U j (fun V => parentBoundaryBandSurplus M n height t V omega) := by
  ext i k
  change descendantsAverage U j (fun V =>
      (coarseBlockMatrix (openCubeSet V) (parentBoundaryBandFrameField M n height t omega)).upperLeft i k)+
    descendantsAverage U j (fun V =>
      (coarseBlockMatrix (openCubeSet V) (parentBoundaryBandFrameField M n height t omega)).lowerRight i k)-
    2*(1 : Mat 2) i k=descendantsAverage U j (fun V => _)
  rw [←descendantsAverage_add,←descendantsAverage_const U j (2*(1 : Mat 2) i k),
    ←old_signed_descendants_average_sub]
  unfold descendantsAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro V hV
  simp only [←coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube V,
    parentBoundaryBandFrameField,
    native_source_band_coarse_matrix_frame M n height t omega (mem_descendantsAtDepth_add hU hV)]
  rfl

/-- The normalized and physical complete traces agree on the same tiling. -/
theorem parent_boundary_band_cell_trace_eq
    (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (omega : Cutoff.CutoffSample 2) (j : ℕ) :
    descendantsAverage U j (fun V => traceDefect (openCubeSet V)
      (parentBoundaryBandFrameField M n height t omega) 1)=
      parentBoundaryBandCellTrace M n height t U j omega := by
  unfold parentBoundaryBandCellTrace descendantsAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro V hV
  unfold traceDefect
  simp only [←coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube V,
    parentBoundaryBandFrameField,
    native_source_band_coarse_matrix_frame M n height t omega (mem_descendantsAtDepth_add hU hV)]
  simp only [frameMatrix,inv_one,one_mul,Matrix.trace_smul,smul_eq_mul]

/-- Positivity and full-trace domination are pathwise, before expectation. -/
theorem parent_boundary_band_directional_nonneg_le
    (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (omega : Cutoff.CutoffSample 2) (j : ℕ) (e : Vec 2) :
    let q := vecDot e (matVecMul (oldSignedPairedDepthMatrix U j
      (parentBoundaryBandFrameField M n height t omega)) e)
    0≤q ∧ q≤parentBoundaryBandCellTrace M n height t U j omega*vecNormSq e := by
  intro q
  let Q := originCube 2 n
  let k := pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t omega)
  let kU := oldSignedCellCoefficient Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) k
  have he := old_signed_paired_depth_matrix_congr U j
    (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n) kU)
    (parentBoundaryBandFrameField M n height t omega)
    (old_signed_cell_frame_coefficient_ae Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU)
      M.nu (Annealed.sigmaBar M n) k)
  have hn (v : Vec 2) : 0≤vecDot v (matVecMul
      (oldSignedPairedDepthMatrix U j (parentBoundaryBandFrameField M n height t omega)) v) := by
    rw [←he]
    exact old_signed_paired_depth_quadratic_nonneg U j M.nu (Annealed.sigmaBar M n)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1 kU v
  refine ⟨hn e,?_⟩
  have hh := old_signed_nonnegative_quadratic_le_trace _ hn e
  rw [old_signed_paired_depth_matrix_trace,parent_boundary_band_cell_trace_eq M n height r U hU] at hh
  exact hh

end
end ASDExplicitGamma.Native
