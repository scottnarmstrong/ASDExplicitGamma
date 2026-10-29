module

public import ASDExplicitGamma.Native.ParentBoundaryBrokenTrace
public import ASDExplicitGamma.Native.OldSignedParentWeakBudgets

/-! Actual broken primal and paired weak budgets of physical parent
minimizers, retaining the complete shifted inverse-weighted trace. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- All four actual primal defects obey the shifted complete trace proxy. -/
theorem parent_boundary_primal_broken_weak_bound (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    descendantsAverage Q depth (fun U => oldSignedPrimalErrorSize Q U nu sigma hnu hsigma k^2) ≤
      rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q a (depth+j))
        (fun j => descendantsAverage Q (depth+j) (fun U => traceDefect (openCubeSet U) a 1)) := by
  intro a
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  simp_rw [old_signed_primal_error_size_sq]
  apply parent_boundary_finite_broken_trace Q depth a hEll
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

/-- Each actual top or bottom pair, with both reciprocal and primal defects,
obeys one shifted complete trace proxy on the comparison partition. -/
theorem parent_boundary_paired_broken_weak_bound (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) (bottom : Bool) :
    let a := responseFramePlanarCoefficientField nu sigma k
    descendantsAverage Q depth (fun U => ∑ c : BlockCoord 2,vectorWeakHaarEnergy U
      (oldSignedPairedDefectField Q nu sigma hnu hsigma k bottom c)) ≤
      rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q a (depth+j))
        (fun j => descendantsAverage Q (depth+j) (fun U => traceDefect (openCubeSet U) a 1)) := by
  intro a
  apply parent_boundary_finite_broken_trace Q depth a
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

/-- Broken primal and reciprocal profiles jointly cost two shifted trace
proxies; both are the actual restrictions of the same parent minimizers. -/
theorem parent_boundary_joint_broken_weak_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    descendantsAverage Q depth (fun U => oldSignedPrimalErrorSize Q U nu sigma hnu hsigma k^2+
      oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k^2) ≤
      2*rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q a (depth+j))
        (fun j => descendantsAverage Q (depth+j) (fun U => traceDefect (openCubeSet U) a 1)) := by
  intro a
  have hh := add_le_add (parent_boundary_paired_broken_weak_bound Q depth nu sigma hnu hsigma k false)
    (parent_boundary_paired_broken_weak_bound Q depth nu sigma hnu hsigma k true)
  rw [←descendantsAverage_add] at hh
  have he (U : TriadicCube 2) :
      (∑ c : BlockCoord 2,vectorWeakHaarEnergy U (oldSignedPairedDefectField Q nu sigma hnu hsigma k false c))+
      (∑ c : BlockCoord 2,vectorWeakHaarEnergy U (oldSignedPairedDefectField Q nu sigma hnu hsigma k true c))=
      oldSignedPrimalErrorSize Q U nu sigma hnu hsigma k^2+
        oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k^2 := by
    rw [old_signed_primal_error_size_sq,old_signed_reciprocal_error_size_sq]
    simp only [Fintype.sum_sum_type,oldSignedPairedDefectField,oldSignedPairLoad,
      Bool.false_eq_true,ite_false,ite_true,Bool.not_false,Bool.not_true,blockBasis]
    ring
  simp_rw [he] at hh
  exact hh.trans_eq (by ring)

end
end ASDExplicitGamma.Native
