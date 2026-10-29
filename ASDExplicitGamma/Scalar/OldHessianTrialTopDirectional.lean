module

public import ASDExplicitGamma.Native.OldSignedDirectionalWeakProxy

/-! The genuine TOP receiver retains the same paired directional budget. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Inverse
noncomputable section

/-- At every depth the TOP first defect and its reciprocal field share the
same actual directional surplus, with both parent energies retained. -/
theorem old_hessian_top_directional_depth_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    oldSignedPrimalProjectionEnergy Q depth nu sigma hnu hsigma k (e,0)+
      oldSignedReciprocalProjectionEnergy Q depth nu sigma hnu hsigma k (e,0) (0,e) ≤
      lemmaVInverseDepthMax Q a depth*vecDot e (matVecMul (oldSignedPairedDepthMatrix Q depth a) e) := by
  intro a
  have hh := old_signed_paired_projection_exact_bound Q depth nu sigma hnu hsigma k (e,0) (0,e)
  apply hh.trans_eq
  rw [←blockVecDot_blockMatVecMul_descendantsAverageBlockMat,
    ←blockVecDot_blockMatVecMul_descendantsAverageBlockMat]
  have he := old_signed_paired_matrix_quadratic
    (descendantsAverageBlockMat Q depth (fun U => coarseBlockMatrix (openCubeSet U) a)) e
  have hcross : blockVecDot (e,0) (0,e).swap=blockVecDot (0,e) (e,0).swap := by
    simp only [blockVecDot,Prod.swap,vecDot_zero_right,zero_add,add_zero]
  rw [hcross]
  rw [add_comm] at he
  rw [he]
  rfl

/-- Complete TOP first/reciprocal weak energy has the same directional
proxy, proved before expectation or isotropic half-trace contraction. -/
theorem old_hessian_top_directional_weak_bound (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    let S := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (e,0)
    let J := oldSignedDualReflection Q nu sigma k S
    vectorWeakHaarEnergy Q (fun x => (S x).1-e)+
      vectorWeakHaarEnergy Q (fun x => (J x).1) ≤
      oldSignedDirectionalProxy Q (responseFramePlanarCoefficientField nu sigma k) e := by
  intro S J
  have hS := (memVectorL2_fst_of_memBlockL2 (Lp.memLp S)).sub (memVectorL2_const e)
  have hJ := memVectorL2_fst_of_memBlockL2
    (old_signed_dual_reflection_memL2 Q nu sigma hnu hsigma k (Lp.memLp S))
  have hp := old_signed_vector_weak_projection_series Q (fun x => (S x).1-e)
    (fun i => memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hS i))
  have hr := old_signed_vector_weak_projection_series Q (fun x => (J x).1)
    (fun i => memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hJ i))
  rw [hp.2,hr.2,←mul_add,←hp.1.tsum_add hr.1]
  unfold oldSignedDirectionalProxy rawWeakTraceProxy
  apply mul_le_mul_of_nonneg_left _
    (sub_nonneg.mpr (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le))
  apply (hp.1.add hr.1).tsum_le_tsum _
    (old_signed_directional_proxy_summable Q nu sigma hnu hsigma k e)
  intro j
  have hh := mul_le_mul_of_nonneg_left
    (old_hessian_top_directional_depth_bound Q j nu sigma hnu hsigma k e)
    (pow_nonneg inverse_history_discount_range.1.le (2*j))
  simpa only [oldSignedPrimalProjectionEnergy,oldSignedReciprocalProjectionEnergy,
    Prod.fst_zero,Pi.zero_apply,sub_zero,Pi.sub_apply,mul_add,mul_assoc,S,J] using hh

end
end ASDExplicitGamma.Scalar
