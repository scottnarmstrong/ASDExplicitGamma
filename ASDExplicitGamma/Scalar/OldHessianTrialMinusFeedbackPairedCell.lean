module

public import ASDExplicitGamma.Native.OldSignedCompleteCellFeedback
public import ASDExplicitGamma.Native.OldSignedMinusFirstDirectionalBudget
public import ASDExplicitGamma.Scalar.OldHessianTrialBottomReciprocalLoad
public import ASDExplicitGamma.Native.OldSignedFlatL2Profiles

/-! Complete bottom-flat derivative feedback with directional affine payment. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Scalar
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The actual minus correction feedback keeps its directional affine
proxy and its compatible oscillation cost through the complete sum. -/
theorem old_hessian_actual_minus_feedback_paired_cell (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U hsub k
    let m := fun n i => oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L n i)
    let A := fun n i => oldSignedCellResidual Q U hsub nu sigma hnu hsigma k
      (oldSignedFlatMinusBlock Q b L n i) (old_signed_flat_minus_block_memL2 Q b L n i)
    let f := fun n => ∑ i : Fin 2,oldSignedEnergyPairing U nu sigma kU
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis (Sum.inr i)))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        ((A n i : Vec 2 → BlockVec 2)-oldSignedFlatMinusBlock Q b L n i))
    Summable f ∧ |∑' n,f n|≤oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
      (Real.sqrt 2+Real.sqrt (oldHessianBottomPairedCellEnergy Q U nu sigma hnu hsigma k))*
      (Real.sqrt (∑' n,∑ i : Fin 2,oldSignedDirectionalProxy U
        (responseFramePlanarCoefficientField nu sigma kU) (m n i).1)+
        (Real.sqrt (oldSignedInverseHistory U a*oldSignedResponseHistory U a)+1)*oldSignedFlatOscillationSize Q U b L false) := by
  intro hsub a kU m A f
  let F := fun n i => oldSignedFlatMinusBlock Q b L n i
  let hF := fun n i => old_signed_flat_minus_block_memL2 Q b L n i
  let v := fun n i => oldSignedCellMinusPotential Q U hsub nu sigma hnu hsigma k b L n i
  have hp := old_signed_actual_minus_first_directional_series Q depth nu sigma hnu hsigma k b L U hU
  have hv (i : Fin 2) : Summable (fun n : whiteBasisIndex => vectorWeakHaarNorm U (v n i).toH1Function.grad^2) :=
    old_signed_finite_series_component _ (fun _ _ => sq_nonneg _) hp.1 i
  have heq : (∑ i : Fin 2,∑' n : whiteBasisIndex,vectorWeakHaarNorm U (v n i).toH1Function.grad^2)=
      ∑' n : whiteBasisIndex,∑ i : Fin 2,vectorWeakHaarNorm U (v n i).toH1Function.grad^2 :=
    (Summable.tsum_finsetSum (fun i _ => hv i)).symm
  have hh := old_signed_complete_cell_correction_feedback Q U hsub nu sigma hnu hsigma k
    (fun i : Fin 2 => blockBasis (Sum.inr i)) b L F hF hv
  have hresult : Summable f ∧ |∑' n,f n|≤oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
      Real.sqrt (∑ i : Fin 2,vectorWeakHaarNorm U
        (oldSignedCellReciprocalPotential Q U hsub nu sigma hnu hsigma k (blockBasis (Sum.inr i))).grad^2)*
      Real.sqrt (∑ i : Fin 2,∑' n : whiteBasisIndex,vectorWeakHaarNorm U (v n i).toH1Function.grad^2) := hh
  rw [heq] at hresult
  have hg := old_hessian_bottom_reciprocal_load_budget Q U hsub nu sigma hnu hsigma k
  have hκ := old_signed_derivative_kappa_nonneg (Triadic.cubeScaleFactor_pos' U).le b L.1
  exact ⟨hresult.1,hresult.2.trans (mul_le_mul (mul_le_mul_of_nonneg_left hg hκ) hp.2
    (Real.sqrt_nonneg _) (mul_nonneg hκ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))))⟩

end
end ASDExplicitGamma.Scalar
