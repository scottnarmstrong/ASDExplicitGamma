module

public import ASDExplicitGamma.Native.ParentBoundaryBandAffineExpectation

/-! The expected normalized diagonal coefficient is common to every source
cell at a fixed depth under the actual whole-sample translation law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Algsuperdiff.Section3
noncomputable section

/-- Actual scalar block means depend only on cell scale, with sigma_n fixed. -/
theorem parent_boundary_band_block_mean_origin (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (U : TriadicCube 2) (plus : Bool) :
    parentBoundaryBandBlockMean M n height t U plus=
      parentBoundaryBandBlockMean M n height t (originCube 2 U.scale) plus := by
  let f := fun omega => parentBoundaryBandNormalizedBlock M n height t (originCube 2 U.scale) plus omega 0 0
  have hf : Measurable f := by
    cases plus
    · exact (parent_boundary_band_diagonal_entry_measurable M n (n+(height:ℤ))
        (fun _ => Real.sqrt t) (originCube 2 U.scale) false 0 0).const_mul _
    · exact (parent_boundary_band_diagonal_entry_measurable M n (n+(height:ℤ))
        (fun _ => Real.sqrt t) (originCube 2 U.scale) true 0 0).const_mul _
  have he (omega) : parentBoundaryBandNormalizedBlock M n height t U plus omega 0 0=
      f (Cutoff.translateCutoffSample (triadicCubeShift U) omega) := by
    unfold parentBoundaryBandNormalizedBlock
    rw [parent_boundary_band_coarse_cell_translate M n (n+(height:ℤ)) (fun _ => Real.sqrt t) U omega]
    rfl
  unfold parentBoundaryBandBlockMean
  simp_rw [he]
  have hi := integral_map (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (Cutoff.measurable_translateCutoffSample (triadicCubeShift U)).aemeasurable hf.aestronglyMeasurable
  rw [Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift U)] at hi
  exact hi.symm

/-- Actual source cells at the same depth have identical scalar block means. -/
theorem parent_boundary_band_block_mean_eq (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t : ℝ) (U V : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) r) (hV : V∈descendantsAtDepth (originCube 2 n) r)
    (plus : Bool) :
    parentBoundaryBandBlockMean M n height t U plus=parentBoundaryBandBlockMean M n height t V plus := by
  rw [parent_boundary_band_block_mean_origin M n height t U,
    parent_boundary_band_block_mean_origin M n height t V,
    scale_eq_sub_of_mem_descendantsAtDepth hU,scale_eq_sub_of_mem_descendantsAtDepth hV]

/-- The literal signed affine expectation has two common scalar coefficients
on the entire finite source tiling. -/
theorem parent_boundary_band_affine_expected_coefficients
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (height : ℕ) (hheight : 1≤height) (r : ℕ) (t b : ℝ) (L : {l : ℝ // 0<l})
    (U0 : TriadicCube 2) (hU0 : U0∈descendantsAtDepth (originCube 2 n) r) :
    (∫ omega,oldSignedFlatAffineContribution (originCube 2 n) r
      (parentBoundaryBandFrameField M n height t omega) b L ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      (parentBoundaryBandBlockMean M n height t U0 false-1)*
        descendantsAverage (originCube 2 n) r (fun U => oldSignedFlatMeanSize (originCube 2 n) U b L true^2)+
      (parentBoundaryBandBlockMean M n height t U0 true-1)*
        descendantsAverage (originCube 2 n) r (fun U => oldSignedFlatMeanSize (originCube 2 n) U b L false^2) := by
  rw [(parent_boundary_band_affine_expectation M h hM n height hheight r t b L).2]
  rw [←descendantsAverage_mul_left,←descendantsAverage_mul_left,←descendantsAverage_add]
  unfold descendantsAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro U hU
  rw [parent_boundary_band_block_mean_eq M n height r t U U0 hU hU0 false,
    parent_boundary_band_block_mean_eq M n height r t U U0 hU hU0 true]

end
end ASDExplicitGamma.Native
