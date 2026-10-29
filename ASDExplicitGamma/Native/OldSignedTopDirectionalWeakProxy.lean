module

public import ASDExplicitGamma.Native.OldSignedDirectionalWeakProxy

/-! The same directional inverse proxy pays top-load paired affine defects. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic Inverse
noncomputable section

/-- The opposite pure loads give the identical coarse quadratic matrix. -/
theorem old_signed_top_paired_matrix_quadratic (A : BlockMat 2) (e : Vec 2) :
    blockVecDot (e,0) (blockMatVecMul A (e,0))+
      blockVecDot (0,e) (blockMatVecMul A (0,e))-2*blockVecDot (e,0) (0,e).swap=
    vecDot e (matVecMul (A.upperLeft+A.lowerRight-(2 : ℝ) • (1 : Mat 2)) e) := by
  simp [blockVecDot,blockMatVecMul,matVecMul,vecDot,Fin.sum_univ_two,Matrix.one_apply]
  ring

/-- The paired top directional projection has the same depth majorant. -/
theorem old_signed_top_directional_depth_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    oldSignedPrimalProjectionEnergy Q depth nu sigma hnu hsigma k (e,0)+
      oldSignedReciprocalProjectionEnergy Q depth nu sigma hnu hsigma k (e,0) (0,e) ≤
      lemmaVInverseDepthMax Q a depth*vecDot e (matVecMul (oldSignedPairedDepthMatrix Q depth a) e) := by
  intro a
  have hh := old_signed_paired_projection_exact_bound Q depth nu sigma hnu hsigma k (e,0) (0,e)
  apply hh.trans_eq
  rw [← blockVecDot_blockMatVecMul_descendantsAverageBlockMat,
    ← blockVecDot_blockMatVecMul_descendantsAverageBlockMat,old_signed_top_paired_matrix_quadratic]
  rfl

/-- Top primal and reciprocal weak energies share the same actual complete
proxy; the two opposite parent energies cancel before the depth sum. -/
theorem old_signed_top_directional_weak_bound (Q : TriadicCube 2)
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
    (old_signed_top_directional_depth_bound Q j nu sigma hnu hsigma k e)
    (pow_nonneg inverse_history_discount_range.1.le (2*j))
  simpa only [oldSignedPrimalProjectionEnergy,oldSignedReciprocalProjectionEnergy,
    Prod.fst_zero,Pi.zero_apply,sub_zero,Pi.sub_apply,mul_add,mul_assoc,S,J] using hh


end
end ASDExplicitGamma.Native
