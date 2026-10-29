module

public import ASDExplicitGamma.Scalar.OldHessianTrialMixedCellFirstSeries
public import ASDExplicitGamma.Scalar.OldHessianTrialBottomReciprocalLoad
public import ASDExplicitGamma.Native.OldSignedCompleteCellFeedback

/-! Complete actual mixed-source derivative feedback on one unchanged fine cell. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Literal cell derivative feedback of the actual coarse-source/fine-projection residual. -/
def oldHessianMixedFeedbackCellMode (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (U : OldSignedCellIndex Q (coarse+1)) : ℝ :=
  ∑ i : Fin 2,oldSignedEnergyPairing U.val nu sigma
    (oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis (.inr i)))
    (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
      (oldSignedCellResidual Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k
        (oldHessianMixedBottomSource Q coarse (coarse+1) nu sigma hnu hsigma k b L n i)
        (old_hessian_mixed_bottom_source_memL2 Q coarse (coarse+1) nu sigma hnu hsigma k b L n i)))

/-- The actual signed cell feedback is absolutely summable and costs its
literal two-bottom reciprocal factor, sharp Df and original inverse history.
Every source and first-corrector convergence input is supplied internally. -/
theorem old_hessian_actual_mixed_cell_feedback (n : ℤ) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (b : ℝ) (L : {l : ℝ // 0<l})
    (U : OldSignedCellIndex (originCube 2 n) (coarse+1)) :
    let Q := originCube 2 n
    let a := responseFramePlanarCoefficientField nu sigma k
    Summable (fun j => oldHessianMixedFeedbackCellMode Q coarse nu sigma hnu hsigma k b L j U) ∧
    |∑' j,oldHessianMixedFeedbackCellMode Q coarse nu sigma hnu hsigma k b L j U|≤
      oldSignedDerivativeKappa (cubeScaleFactor U.val) b L.val*
        (Real.sqrt 2+Real.sqrt (oldHessianBottomPairedCellEnergy Q U.val nu sigma hnu hsigma k))*
        (((63/50:ℝ)*oldSignedInverseHistory U.val a)*Real.sqrt (∑' p,
          vectorPositiveHaarEnergy U.val (oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L p))) := by
  intro Q a
  let hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  let F := fun j i => oldHessianMixedBottomSource Q coarse (coarse+1) nu sigma hnu hsigma k b L j i
  let hF := fun j i => old_hessian_mixed_bottom_source_memL2 Q coarse (coarse+1) nu sigma hnu hsigma k b L j i
  have hfirst := old_hessian_mixed_cell_first_series n coarse nu sigma hnu hsigma k b L U
  have hh := old_signed_complete_cell_correction_feedback Q U.val hsub nu sigma hnu hsigma k
    (fun i : Fin 2 => blockBasis (.inr i)) b L F hF hfirst.1
  have hz (j : whiteBasisIndex) (i : Fin 2) : oldSignedPointwiseShear
      (q3Convolution b L h3Zero (whiteBasis j)) (F j i)=0 := by
    funext x
    have hzero : (F j i x).1=0 := by
      simp only [F,oldHessianMixedBottomSource,oldHessianMixedSource,
        oldSignedLocalizedPotentialShear,Prod.fst_add,zero_add]
    change (0,-(_ • matVecMul responsePlanarJ (F j i x).1))=(0,0)
    rw [hzero,matVecMul_zero,smul_zero,neg_zero]
  have he (j : whiteBasisIndex) :
      (∑ i : Fin 2,oldSignedEnergyPairing U.val nu sigma (oldSignedCellCoefficient Q U.val hsub k)
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis (.inr i)))
        (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis j))
          ((oldSignedCellResidual Q U.val hsub nu sigma hnu hsigma k (F j i) (hF j i) : Vec 2 → BlockVec 2)-F j i)))=
      oldHessianMixedFeedbackCellMode Q coarse nu sigma hnu hsigma k b L j U := by
    apply Finset.sum_congr rfl
    intro i _
    rw [map_sub,hz,sub_zero]
  simp_rw [he] at hh
  have hrec := old_hessian_bottom_reciprocal_load_budget Q U.val hsub nu sigma hnu hsigma k
  have hκ := old_signed_derivative_kappa_nonneg (Triadic.cubeScaleFactor_pos' U.val).le b L.val
  exact ⟨hh.1,hh.2.trans (mul_le_mul (mul_le_mul_of_nonneg_left hrec hκ) hfirst.2
    (Real.sqrt_nonneg _) (mul_nonneg hκ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))))⟩

end
end ASDExplicitGamma.Scalar
