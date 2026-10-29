module

public import ASDExplicitGamma.Native.OldSignedShiftedTraceProxy
public import ASDExplicitGamma.Native.OldSignedParentWeakBudgets

/-! Actual parent first and reciprocal errors on the source tiling. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic Inverse
noncomputable section

/-- Each actual load pair, primal and reciprocal together, is bounded by
one complete physical inverse-weighted trace proxy. No estimated premise. -/
theorem old_signed_tiled_paired_weak_trace_bound (Q : TriadicCube 2) (mesh : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) (bottom : Bool) :
    let a := responseFramePlanarCoefficientField nu sigma k
    descendantsAverage Q mesh (fun U => ∑ c : BlockCoord 2,vectorWeakHaarEnergy U
      (oldSignedPairedDefectField Q nu sigma hnu hsigma k bottom c)) ≤
      rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q a (mesh+j))
        (fun j => descendantsAverage Q (mesh+j) (fun U => traceDefect (openCubeSet U) a 1)) := by
  intro a
  apply old_signed_tiled_weak_trace_bound Q mesh a
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) nu sigma hnu hsigma k)
    _ (old_signed_paired_defect_memLp Q nu sigma hnu hsigma k bottom)
  intro j
  cases bottom
  · have hh := old_signed_top_paired_projection_trace_bound Q j nu sigma hnu hsigma k
    simpa only [oldSignedPairedDefectField,oldSignedPairLoad,Bool.false_eq_true,ite_false,
      Bool.not_false,ite_true,Fintype.sum_sum_type,oldSignedPrimalProjectionEnergy,
      oldSignedReciprocalProjectionEnergy,Finset.sum_add_distrib,Pi.sub_apply,a] using hh
  · have hh := old_signed_bottom_paired_projection_trace_bound Q j nu sigma hnu hsigma k
    simpa only [oldSignedPairedDefectField,oldSignedPairLoad,ite_true,Bool.not_true,
      Bool.false_eq_true,ite_false,Fintype.sum_sum_type,oldSignedPrimalProjectionEnergy,
      oldSignedReciprocalProjectionEnergy,Finset.sum_add_distrib,Pi.sub_apply,a] using hh

/-- The four actual parent first defects cost one complete trace proxy. -/
theorem old_signed_tiled_parent_primal_weak_bound (Q : TriadicCube 2) (mesh : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    descendantsAverage Q mesh (fun U => oldSignedPrimalErrorSize Q U nu sigma hnu hsigma k^2) ≤
      rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q a (mesh+j))
        (fun j => descendantsAverage Q (mesh+j) (fun U => traceDefect (openCubeSet U) a 1)) := by
  intro a
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  simp_rw [old_signed_primal_error_size_sq]
  apply old_signed_tiled_weak_trace_bound Q mesh a hEll
  · intro c i
    have hm := (memVectorL2_fst_of_memBlockL2
      (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c)))).sub
      (memVectorL2_const (blockBasis c).1)
    exact memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hm i)
  · intro j
    have hh := old_signed_primal_projection_trace_gap Q j nu sigma hnu hsigma k
    exact hh.trans (mul_le_mul_of_nonneg_left
      (sub_le_self _ (Cold.coarse_square_traceDefect_nonneg Q hEll))
      (lemmaVInverseDepthMax_nonneg Q a j))

/-- The actual four-load primal and reciprocal profiles jointly cost two
trace proxies. This keeps their correlation until after the paired sum. -/
theorem old_signed_tiled_parent_paired_weak_bound (Q : TriadicCube 2) (mesh : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    descendantsAverage Q mesh (fun U => oldSignedPrimalErrorSize Q U nu sigma hnu hsigma k^2+
      oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k^2) ≤
      2*rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q a (mesh+j))
        (fun j => descendantsAverage Q (mesh+j) (fun U => traceDefect (openCubeSet U) a 1)) := by
  intro a
  have hh := add_le_add (old_signed_tiled_paired_weak_trace_bound Q mesh nu sigma hnu hsigma k false)
    (old_signed_tiled_paired_weak_trace_bound Q mesh nu sigma hnu hsigma k true)
  simp_rw [old_signed_primal_error_size_sq,old_signed_reciprocal_error_size_sq]
  rw [descendantsAverage_add]
  simp only [Fintype.sum_sum_type,oldSignedPairedDefectField,oldSignedPairLoad,
    Bool.false_eq_true,ite_false,ite_true,Bool.not_false,Bool.not_true,blockBasis,
    descendantsAverage_add] at hh ⊢
  convert hh using 1 <;> ring

end
end ASDExplicitGamma.Native
