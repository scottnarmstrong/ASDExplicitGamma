module

public import ASDExplicitGamma.Native.ParentBoundaryBandBlockLaw
public import ASDExplicitGamma.Native.ParentBoundaryAffineSeries
public import ASDExplicitGamma.Native.ParentBoundaryBandDirectionalFrame
public import ASDExplicitGamma.Native.OldSignedAffineFamilyAssembly

/-! Exact expectations of literal signed affine source-cell mode series. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- One actual physical affine mode has exactly the corresponding positive
block quadratic minus its deterministic mean-square norm. -/
theorem parent_boundary_band_affine_mode_eq (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) r)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) (i : whiteBasisIndex)
    (col : Fin 2) (omega : Cutoff.CutoffSample 2) :
    let p := oldSignedBlockMean U (oldSignedFlatInput (originCube 2 n) b L plus i col)
    let e := if plus then p.2 else p.1
    blockVecDot p (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
      (parentBoundaryBandFrameField M n height t omega)) p)-blockVecDot p p=
      vecDot e (matVecMul (parentBoundaryBandNormalizedBlock M n height t U (!plus) omega) e)-vecNormSq e := by
  intro p e
  simp only [←coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube U,parentBoundaryBandFrameField]
  rw [native_source_band_coarse_matrix_frame M n height t omega hU]
  cases plus <;> simp [e,p,oldSignedBlockMean,oldSignedFlatInput,oldSignedFlatPlusBlock,
    oldSignedFlatMinusBlock,cubeAverage_const,parentBoundaryBandNormalizedBlock,
    blockVecDot,blockMatVecMul,vecDot,vecNormSq,matVecMul]

/-- Every literal signed affine column is integrable and has its exact
expected block coefficient. No positivity of the deviation is asserted. -/
theorem parent_boundary_band_affine_column_integral
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (height : ℕ) (hheight : 1≤height) (r : ℕ) (U : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) r) (t b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) (col : Fin 2) :
    let p := fun i => oldSignedBlockMean U (oldSignedFlatInput (originCube 2 n) b L plus i col)
    let f := fun omega => ∑' i,(blockVecDot (p i) (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
      (parentBoundaryBandFrameField M n height t omega)) (p i))-blockVecDot (p i) (p i))
    Integrable f (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ omega,f omega ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      (parentBoundaryBandBlockMean M n height t U (!plus)-1)*∑' i,blockVecDot (p i) (p i) := by
  intro p f
  let E := fun i => if plus then (p i).2 else (p i).1
  have he (i) : vecNormSq (E i)=blockVecDot (p i) (p i) := by
    cases plus <;> simp [E,p,oldSignedBlockMean,oldSignedFlatInput,oldSignedFlatPlusBlock,
      oldSignedFlatMinusBlock,cubeAverage_const,blockVecDot,vecDot,vecNormSq]
  have hs : Summable (fun i => vecNormSq (E i)) := by
    simp_rw [he]
    cases plus
    · exact old_signed_flat_minus_mean_series (originCube 2 n) r b L col U hU
    · exact old_signed_flat_plus_mean_series (originCube 2 n) r b L col U hU
  have hb := parent_boundary_band_block_scalar_law M h hM n height hheight r U hU t (!plus)
  have hm := (parent_boundary_band_block_mean M h hM n height hheight r U hU t (!plus)).2
  have hh := parent_boundary_signed_affine_family_integral (Cutoff.cutoffSampleLaw M).toMeasure
    (parentBoundaryBandNormalizedBlock M n height t U (!plus)) hb.1
    (parent_boundary_band_block_nonneg M n height t U (!plus))
    (parentBoundaryBandBlockMean M n height t U (!plus)) hm E hs
  have hf : f=(fun omega => ∑' i,(vecDot (E i)
      (matVecMul (parentBoundaryBandNormalizedBlock M n height t U (!plus) omega) (E i))-vecNormSq (E i))) := by
    funext omega
    apply tsum_congr
    intro i
    exact parent_boundary_band_affine_mode_eq M n height r U hU t b L plus i col omega
  rw [hf]
  rw [show (∑' i,vecNormSq (E i))=(∑' i,blockVecDot (p i) (p i)) from tsum_congr he] at hh
  exact hh

end
end ASDExplicitGamma.Native
