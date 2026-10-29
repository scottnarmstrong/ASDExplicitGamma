module

public import ASDExplicitGamma.Native.OldSignedAffineInverseBlock
public import ASDExplicitGamma.Native.OldSignedSourceCellFrame
public import ASDExplicitGamma.Native.OldSignedQ1WeakEnvelope

/-! Exact trace relation between the two stationary signed affine coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Variational Inverse Algsuperdiff.Section3
noncomputable section

/-- The depth-zero paired matrix is exactly the two physical diagonal
blocks minus their affine identity. -/
theorem old_signed_paired_zero_entry (U : TriadicCube 2) (a : CoeffField 2) (i : Fin 2) :
    vecDot (basisVec i) (matVecMul (oldSignedPairedDepthMatrix U 0 a) (basisVec i))=
      (coarseBlockMatrix (openCubeSet U) a).upperLeft i i+
      (coarseBlockMatrix (openCubeSet U) a).lowerRight i i-2 := by
  fin_cases i <;> simp [oldSignedPairedDepthMatrix,descendantsAverageBlockMat,descendantsAverageMat,
    descendantsAverage,descendantsAtDepth_zero,vecDot,matVecMul,basisVec]

/-- The two literal scalar block deviations add to half the actual trace
mean on the source cell. No sign assumption is made on either deviation. -/
theorem old_signed_affine_block_trace_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (r : ℕ) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0≤t ∧ t≤1) :
    (∫ ω,rawWeakTraceSequence M n U t ω 0 ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      2*((parentBoundaryBandBlockMean M n 1 t U true-1)+
        (parentBoundaryBandBlockMean M n 1 t U false-1)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let P := fun ω => parentBoundaryBandNormalizedBlock M n 1 t U true ω 0 0
  let N := fun ω => parentBoundaryBandNormalizedBlock M n 1 t U false ω 0 0
  have hp := (parent_boundary_band_block_scalar_law M h hM n 1 (by norm_num) r U hU t true).1 0 0
  have hn := (parent_boundary_band_block_scalar_law M h hM n 1 (by norm_num) r U hU t false).1 0 0
  have hh := old_signed_source_directional_mean M n r U hU t ht 0 (basisVec 0)
  have he (ω : Cutoff.CutoffSample 2) : vecDot (basisVec 0)
      (matVecMul (oldSignedPairedDepthMatrix U 0 (oldSignedPartialFrameField M n 1 t ω)) (basisVec 0))=
        P ω+N ω-2 := by
    rw [old_signed_paired_zero_entry]
    dsimp only [P,N]
    rw [old_signed_actual_normalized_block M n r U hU t ω true,
      old_signed_actual_normalized_block M n r U hU t ω false]
    rfl
  simp_rw [he] at hh
  have hi : Integrable (fun ω => P ω+N ω) μ := hp.add hn
  rw [integral_sub hi (integrable_const 2),integral_add hp hn] at hh
  have hnorm : vecNormSq (basisVec (0:Fin 2))=1 := vecNormSq_basisVec 0
  have hc : (∫ _ : Cutoff.CutoffSample 2,(2:ℝ) ∂μ)=2 := by simp
  rw [hnorm,mul_one,hc] at hh
  change _=2*(((∫ ω,P ω ∂μ)-1)+((∫ ω,N ω ∂μ)-1))
  linarith only [hh]

end
end ASDExplicitGamma.Native
