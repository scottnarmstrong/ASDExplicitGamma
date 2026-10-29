module

public import ASDExplicitGamma.Native.OldSignedPairedProjection
public import ASDExplicitGamma.Native.OldSignedPairedProjectionTrace

/-! Coarse-matrix majorant for each paired directional projection.
This is the physical matrix whose expected half-trace enters the OLD panel. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational
noncomputable section

/-- The sum of the two actual child diagonal coarse blocks minus the affine
identity payment. Its trace is the actual four-load descendant trace. -/
def oldSignedPairedDepthMatrix (Q : TriadicCube 2) (j : ℕ) (a : CoeffField 2) : Mat 2 :=
  let A := descendantsAverageBlockMat Q j (fun U => coarseBlockMatrix (openCubeSet U) a)
  A.upperLeft+A.lowerRight-(2 : ℝ) • (1 : Mat 2)

/-- Exact pure-load quadratic form of the paired matrix. -/
theorem old_signed_paired_matrix_quadratic (A : BlockMat 2) (e : Vec 2) :
    blockVecDot (0,e) (blockMatVecMul A (0,e))+
      blockVecDot (e,0) (blockMatVecMul A (e,0))-2*blockVecDot (0,e) (e,0).swap=
    vecDot e (matVecMul (A.upperLeft+A.lowerRight-(2 : ℝ) • (1 : Mat 2)) e) := by
  simp [blockVecDot,blockMatVecMul,matVecMul,vecDot,Fin.sum_univ_two,Matrix.one_apply]
  ring

/-- The actual paired bottom directional projection is bounded by the
quadratic coarse majorant, before any averaging or isotropy is used. -/
theorem old_signed_bottom_directional_depth_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    oldSignedPrimalProjectionEnergy Q depth nu sigma hnu hsigma k (0,e)+
      oldSignedReciprocalProjectionEnergy Q depth nu sigma hnu hsigma k (0,e) (e,0) ≤
      lemmaVInverseDepthMax Q a depth*vecDot e (matVecMul (oldSignedPairedDepthMatrix Q depth a) e) := by
  intro a
  have hh := old_signed_paired_projection_exact_bound Q depth nu sigma hnu hsigma k (0,e) (e,0)
  apply hh.trans_eq
  rw [← blockVecDot_blockMatVecMul_descendantsAverageBlockMat,
    ← blockVecDot_blockMatVecMul_descendantsAverageBlockMat,old_signed_paired_matrix_quadratic]
  rfl

/-- Trace of the coarse directional majorant is exactly the same complete
four-load trace used by the weak-history budget. -/
theorem old_signed_paired_depth_matrix_trace (Q : TriadicCube 2) (depth : ℕ) (a : CoeffField 2) :
    Matrix.trace (oldSignedPairedDepthMatrix Q depth a)=
      descendantsAverage Q depth (fun U => traceDefect (openCubeSet U) a 1) := by
  change (∑ i : Fin 2,(descendantsAverage Q depth (fun U =>
    (coarseBlockMatrix (openCubeSet U) a).upperLeft i i)+
    descendantsAverage Q depth (fun U => (coarseBlockMatrix (openCubeSet U) a).lowerRight i i)-2*(1 : Mat 2) i i))=_
  simp only [Matrix.one_apply_eq,mul_one]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← Homogenization.descendantsAverage_sum,← Homogenization.descendantsAverage_sum]
  simp only [traceDefect,inv_one,one_mul,Matrix.trace,Matrix.diag_apply]
  rw [old_signed_descendants_average_sub,descendantsAverage_add,descendantsAverage_const]
  norm_num

end
end ASDExplicitGamma.Native
