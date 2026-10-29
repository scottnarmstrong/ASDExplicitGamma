module

public import ASDExplicitGamma.Native.OldSignedPartialFrameHistory
public import ASDExplicitGamma.Native.OldSignedDescendantDirectionalMean
public import ASDExplicitGamma.Native.OldSignedDirectionalProxyCongr

/-! Fixed-frame directional matrices and traces on actual source descendants. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Algsuperdiff.Section3
noncomputable section

/-- All descendants of a source cell retain the same physical completed frame. -/
theorem old_signed_source_descendant_frame (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ)
    (V : TriadicCube 2) (hV : V ∈ descendantsAtDepth U j) :
    coarseBlockMatrix (openCubeSet V) (oldSignedPartialFrameField M n 1 t ω)=
      frameMatrix (Annealed.sigmaBar M n)
        (coarseBlockMatrix (cubeSet V) (Model.partialInsertedCoefficient M n t ω).toFun) := by
  rw [←coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube V]
  simpa only [Nat.cast_one,add_sub_cancel_right] using
    old_signed_partial_cell_frame M n 1 t ω V (r+j) (mem_descendantsAtDepth_add hU hV)

/-- The actual source directional matrix is the physical coarse matrix on
that same descendant tiling, in sigma_n rather than the molecular frame. -/
theorem old_signed_source_directional_matrix (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    oldSignedPairedDepthMatrix U j (oldSignedPartialFrameField M n 1 t ω)=
      descendantsAverageMat U j (fun V => oldSignedCoarseDirectionalMatrix V
        (Model.partialInsertedCoefficient M n t ω).toFun (Annealed.sigmaBar M n)) := by
  ext i k
  change descendantsAverage U j (fun V =>
      (coarseBlockMatrix (openCubeSet V) (oldSignedPartialFrameField M n 1 t ω)).upperLeft i k)+
    descendantsAverage U j (fun V =>
      (coarseBlockMatrix (openCubeSet V) (oldSignedPartialFrameField M n 1 t ω)).lowerRight i k)-
    2*(1 : Mat 2) i k=descendantsAverage U j (fun V => _)
  rw [←descendantsAverage_add,←descendantsAverage_const U j (2*(1 : Mat 2) i k),
    ←old_signed_descendants_average_sub]
  unfold descendantsAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro V hV
  rw [old_signed_source_descendant_frame M n r U hU t ω j V hV]
  rfl

/-- The source trace sequence is exactly the raw common-tiling average. -/
theorem old_signed_source_trace_depth (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    descendantsAverage U j (fun V => traceDefect (openCubeSet V)
      (oldSignedPartialFrameField M n 1 t ω) 1)=rawWeakTraceSequence M n U t ω j := by
  change _=oldSignedCellAverage U j (fun V => rawCubeFourLoadTrace M n V.val t ω)
  rw [old_signed_cell_average_eq_descendantsAverage U j (fun V => rawCubeFourLoadTrace M n V t ω)]
  unfold descendantsAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro V hV
  unfold rawCubeFourLoadTrace traceDefect
  rw [old_signed_source_descendant_frame M n r U hU t ω j V hV]
  simp only [frameMatrix,inv_one,one_mul,Matrix.trace_smul,smul_eq_mul]

/-- The physical unweighted directional mean retains its half-trace factor
on every source cell and every descendant depth. -/
theorem old_signed_source_directional_mean (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (j : ℕ) (e : Vec 2) :
    (∫ ω,vecDot e (matVecMul (oldSignedPairedDepthMatrix U j
      (oldSignedPartialFrameField M n 1 t ω)) e) ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      (1/2:ℝ)*(∫ ω,rawWeakTraceSequence M n U t ω j
        ∂(Cutoff.cutoffSampleLaw M).toMeasure)*vecNormSq e := by
  simp_rw [old_signed_source_directional_matrix M n r U hU]
  rw [old_signed_descendant_directional_mean M n U j t ht]
  congr 2
  apply integral_congr_ae
  filter_upwards with ω
  exact (old_signed_cell_average_eq_descendantsAverage U j
    (fun V => rawCubeFourLoadTrace M n V t ω)).symm

end
end ASDExplicitGamma.Native
