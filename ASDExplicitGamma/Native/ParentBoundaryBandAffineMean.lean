module

public import ASDExplicitGamma.Native.ParentBoundaryBandAffineCell

/-! Exact complete signed affine expectations on the actual finite tiling. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- The literal affine mean deviation of one complete signed flat family. -/
def parentBoundaryBandAffineFamily (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) (omega : Cutoff.CutoffSample 2) : ℝ :=
  ∑' i,descendantsAverage (originCube 2 n) r (fun U => ∑ col : Fin 2,
    let p := oldSignedBlockMean U (oldSignedFlatInput (originCube 2 n) b L plus i col)
    blockVecDot p (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
      (parentBoundaryBandFrameField M n height t omega)) p)-blockVecDot p p)

/-- The complete signed source-cell mean has its actual scalar block
coefficient, and is integrable without a deviation sign hypothesis. -/
theorem parent_boundary_band_affine_cell_integral
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (height : ℕ) (hheight : 1≤height) (r : ℕ) (U : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) r) (t b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) :
    let f := fun omega => ∑' i,∑ col : Fin 2,
      let p := oldSignedBlockMean U (oldSignedFlatInput (originCube 2 n) b L plus i col)
      blockVecDot p (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
        (parentBoundaryBandFrameField M n height t omega)) p)-blockVecDot p p
    Integrable f (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ omega,f omega ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      (parentBoundaryBandBlockMean M n height t U (!plus)-1)*oldSignedFlatMeanSize (originCube 2 n) U b L plus^2 := by
  intro f
  let p := fun i col => oldSignedBlockMean U (oldSignedFlatInput (originCube 2 n) b L plus i col)
  let q := fun col omega => ∑' i,(blockVecDot (p i col) (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
    (parentBoundaryBandFrameField M n height t omega)) (p i col))-blockVecDot (p i col) (p i col))
  have hcol (col) := parent_boundary_band_affine_column_integral M h hM n height hheight r U hU t b L plus col
  have hs (col) : Summable (fun i => blockVecDot (p i col) (p i col)) := by
    cases plus
    · exact old_signed_flat_minus_mean_series (originCube 2 n) r b L col U hU
    · exact old_signed_flat_plus_mean_series (originCube 2 n) r b L col U hU
  have he (omega) : f omega=∑ col : Fin 2,q col omega :=
    Summable.tsum_finsetSum (fun col _ => old_signed_affine_deviation_summable _ (fun i => p i col) (hs col))
  have hnorm : oldSignedFlatMeanSize (originCube 2 n) U b L plus^2=
      ∑ col : Fin 2,∑' i,blockVecDot (p i col) (p i col) := by
    unfold oldSignedFlatMeanSize
    change Real.sqrt (∑' i,∑ col : Fin 2,blockVecDot (p i col) (p i col))^2=_
    have hn : 0≤∑' i,∑ col : Fin 2,blockVecDot (p i col) (p i col) :=
      tsum_nonneg (fun i => Finset.sum_nonneg (fun col _ =>
        add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)))
    rw [Real.sq_sqrt hn,Summable.tsum_finsetSum (fun col _ => hs col)]
  have hf : f=(fun omega => ∑ col : Fin 2,q col omega) := funext he
  rw [hf]
  refine ⟨integrable_finsetSum _ (fun col _ => (hcol col).1),?_⟩
  rw [integral_finsetSum _ (fun col _ => (hcol col).1),hnorm,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun col _ => (hcol col).2)

/-- Each whole signed affine family commutes with the genuine finite
spatial partition and expectation. All infinite mode sums converge first. -/
theorem parent_boundary_band_affine_family_integral
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (height : ℕ) (hheight : 1≤height) (r : ℕ) (t b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) :
    Integrable (parentBoundaryBandAffineFamily M n height r t b L plus) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ omega,parentBoundaryBandAffineFamily M n height r t b L plus omega
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      descendantsAverage (originCube 2 n) r (fun U =>
        (parentBoundaryBandBlockMean M n height t U (!plus)-1)*oldSignedFlatMeanSize (originCube 2 n) U b L plus^2) := by
  let Q := originCube 2 n
  let f := fun U omega => ∑' i,∑ col : Fin 2,
    let p := oldSignedBlockMean U (oldSignedFlatInput Q b L plus i col)
    blockVecDot p (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
      (parentBoundaryBandFrameField M n height t omega)) p)-blockVecDot p p
  have hp (U) (hU : U∈descendantsAtDepth Q r) :=
    parent_boundary_band_affine_cell_integral M h hM n height hheight r U hU t b L plus
  have he (omega) : parentBoundaryBandAffineFamily M n height r t b L plus omega=
      descendantsAverage Q r (fun U => f U omega) :=
    (old_signed_partition_series Q r _ (old_signed_flat_affine_family_cell_summable Q r
      (parentBoundaryBandFrameField M n height t omega) b L plus)).2
  have hfun : parentBoundaryBandAffineFamily M n height r t b L plus=
      (fun omega => descendantsAverage Q r (fun U => f U omega)) := funext he
  rw [hfun]
  refine ⟨?_,?_⟩
  · unfold descendantsAverage
    exact (integrable_finsetSum _ (fun U hU => (hp U hU).1)).const_mul _
  · rw [old_signed_integral_descendants_average _ Q r f (fun U hU => (hp U hU).1)]
    unfold descendantsAverage
    dsimp only
    congr 1
    exact Finset.sum_congr rfl (fun U hU => (hp U hU).2)

end
end ASDExplicitGamma.Native
