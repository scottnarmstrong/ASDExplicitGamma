module

public import ASDExplicitGamma.Native.OldSignedCompleteCellFeedback
public import ASDExplicitGamma.Native.OldSignedPlusFirstBudget
public import ASDExplicitGamma.Native.OldSignedReciprocalLoadBudget
public import ASDExplicitGamma.Native.OldSignedFlatL2Profiles

/-! The complete actual top-flat derivative-only feedback, with zero
boundary first potentials and the literal AN full local L2 flat size. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- The actual A feedback costs kappa G_U (sqrt(theta_U) x_U+D B_U OmegaPlus_U).
No potential, convergence or estimated norm is a premise. -/
theorem old_signed_actual_plus_feedback_bill (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U hsub k
    let A := fun n i => oldSignedCellResidual Q U hsub nu sigma hnu hsigma k
      (oldSignedFlatPlusBlock Q b L n i) (old_signed_flat_plus_block_memL2 Q b L n i)
    let f := fun n => ∑ i : Fin 2,oldSignedEnergyPairing U nu sigma kU
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis (Sum.inl i)))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) (A n i))
    Summable f ∧ |∑' n,f n|≤oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
      oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k*
      (Real.sqrt (oldSignedCorrectorHistory U a)*oldSignedFlatL2Size Q U b L true+
        (1+inverseHistoryDiscount)*oldSignedInverseHistory U a*oldSignedFlatOscillationSize Q U b L true) := by
  intro hsub a kU A f
  let F := fun n i => oldSignedFlatPlusBlock Q b L n i
  let hF := fun n i => old_signed_flat_plus_block_memL2 Q b L n i
  let v := fun n i => oldSignedCellPlusPotential Q U hsub nu sigma hnu hsigma k b L n i
  have hp := old_signed_actual_plus_first_series Q depth nu sigma hnu hsigma k b L U hU
  have hv (i : Fin 2) : Summable (fun n : whiteBasisIndex => vectorWeakHaarNorm U (v n i).toH1Function.grad^2) :=
    old_signed_finite_series_component _ (fun _ _ => sq_nonneg _) hp.1 i
  have heq : (∑ i : Fin 2,∑' n : whiteBasisIndex,vectorWeakHaarNorm U (v n i).toH1Function.grad^2)=
      ∑' n : whiteBasisIndex,∑ i : Fin 2,vectorWeakHaarNorm U (v n i).toH1Function.grad^2 :=
    (Summable.tsum_finsetSum (fun i _ => hv i)).symm
  have hh := old_signed_complete_cell_correction_feedback Q U hsub nu sigma hnu hsigma k
    (fun i : Fin 2 => blockBasis (Sum.inl i)) b L F hF hv
  let fc := fun n => ∑ i : Fin 2,oldSignedEnergyPairing U nu sigma kU
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis (Sum.inl i)))
    (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
      ((A n i : Vec 2 → BlockVec 2)-F n i))
  have hfc : fc=f := by
    funext n
    apply Finset.sum_congr rfl
    intro i _
    have hz : oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) (F n i)=0 := by
      funext x
      change (0,-(_ • matVecMul responsePlanarJ 0))=(0,0)
      rw [matVecMul_zero,smul_zero,neg_zero]
    rw [map_sub,hz,sub_zero]
  have hresult : Summable fc ∧ |∑' n,fc n|≤oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
      Real.sqrt (∑ i : Fin 2,vectorWeakHaarNorm U
        (oldSignedCellReciprocalPotential Q U hsub nu sigma hnu hsigma k (blockBasis (Sum.inl i))).grad^2)*
      Real.sqrt (∑ i : Fin 2,∑' n : whiteBasisIndex,vectorWeakHaarNorm U (v n i).toH1Function.grad^2) := hh
  rw [hfc,heq] at hresult
  have hb := hp.2.trans (add_le_add (mul_le_mul_of_nonneg_left
    (old_signed_flat_mean_size_le_l2 Q depth b L true U hU) (Real.sqrt_nonneg _)) le_rfl)
  have hg := old_signed_actual_top_reciprocal_budget Q U hsub nu sigma hnu hsigma k
  have hκ := old_signed_derivative_kappa_nonneg (Triadic.cubeScaleFactor_pos' U).le b L.1
  exact ⟨hresult.1,hresult.2.trans (mul_le_mul (mul_le_mul_of_nonneg_left hg hκ) hb
    (Real.sqrt_nonneg _) (mul_nonneg hκ (Real.sqrt_nonneg _)))⟩

end
end ASDExplicitGamma.Native
