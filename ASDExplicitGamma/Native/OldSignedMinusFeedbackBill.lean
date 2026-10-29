module

public import ASDExplicitGamma.Native.OldSignedCompleteCellFeedback
public import ASDExplicitGamma.Native.OldSignedMinusFirstBudget
public import ASDExplicitGamma.Native.OldSignedReciprocalLoadBudget
public import ASDExplicitGamma.Native.OldSignedFlatL2Profiles

/-! The complete actual bottom-flat derivative-only feedback, with zero
boundary first potentials and the literal AN full local L2 flat size. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- The actual minus correction feedback costs
kappa (sqrt(2)+G_U) (sqrt(theta_U) y_U+(sqrt(B_U M_U)+1) OmegaMinus_U).
No potential, convergence or estimated norm is a premise. -/
theorem old_signed_actual_minus_feedback_bill (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U hsub k
    let A := fun n i => oldSignedCellResidual Q U hsub nu sigma hnu hsigma k
      (oldSignedFlatMinusBlock Q b L n i) (old_signed_flat_minus_block_memL2 Q b L n i)
    let f := fun n => ∑ i : Fin 2,oldSignedEnergyPairing U nu sigma kU
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis (Sum.inr i)))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        ((A n i : Vec 2 → BlockVec 2)-oldSignedFlatMinusBlock Q b L n i))
    Summable f ∧ |∑' n,f n|≤oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
      (Real.sqrt 2+oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k)*
      (Real.sqrt (oldSignedCorrectorHistory U a)*oldSignedFlatL2Size Q U b L false+
        (Real.sqrt (oldSignedInverseHistory U a*oldSignedResponseHistory U a)+1)*oldSignedFlatOscillationSize Q U b L false) := by
  intro hsub a kU A f
  let F := fun n i => oldSignedFlatMinusBlock Q b L n i
  let hF := fun n i => old_signed_flat_minus_block_memL2 Q b L n i
  let v := fun n i => oldSignedCellMinusPotential Q U hsub nu sigma hnu hsigma k b L n i
  have hp := old_signed_actual_minus_first_series Q depth nu sigma hnu hsigma k b L U hU
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
  have hb := hp.2.trans (add_le_add (mul_le_mul_of_nonneg_left
    (old_signed_flat_mean_size_le_l2 Q depth b L false U hU) (Real.sqrt_nonneg _)) le_rfl)
  have hg : Real.sqrt (∑ i : Fin 2,vectorWeakHaarNorm U
      (oldSignedCellReciprocalPotential Q U hsub nu sigma hnu hsigma k (blockBasis (Sum.inr i))).grad^2) ≤
      Real.sqrt 2+oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k := by
    apply le_trans _ (old_signed_actual_reciprocal_load_budget Q U hsub nu sigma hnu hsigma k)
    apply Real.sqrt_le_sqrt
    rw [Fintype.sum_sum_type]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hκ := old_signed_derivative_kappa_nonneg (Triadic.cubeScaleFactor_pos' U).le b L.1
  exact ⟨hresult.1,hresult.2.trans (mul_le_mul (mul_le_mul_of_nonneg_left hg hκ) hb
    (Real.sqrt_nonneg _) (mul_nonneg hκ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))))⟩

end
end ASDExplicitGamma.Native
