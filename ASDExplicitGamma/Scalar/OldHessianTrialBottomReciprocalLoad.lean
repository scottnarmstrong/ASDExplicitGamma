module

public import ASDExplicitGamma.Scalar.OldHessianTrialParentBottomPair
public import ASDExplicitGamma.Native.OldSignedReciprocalLoadBudget

/-! Exact two-bottom-load reciprocal factor in the mixed OLD feedback. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section

/-- The two genuine restricted parent reciprocal gradients cost sqrt2
plus the same paired bottom error which is paid by a single OLD proxy. -/
theorem old_hessian_bottom_reciprocal_load_budget (Q U : TriadicCube 2)
    (hsub : openCubeSet U⊆openCubeSet Q) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    Real.sqrt (∑ i : Fin 2,vectorWeakHaarNorm U
      (oldSignedCellReciprocalPotential Q U hsub nu sigma hnu hsigma k (blockBasis (.inr i))).grad^2)≤
      Real.sqrt 2+Real.sqrt (oldHessianBottomPairedCellEnergy Q U nu sigma hnu hsigma k) := by
  let g := fun i : Fin 2 => (oldSignedCellReciprocalPotential Q U hsub nu sigma hnu hsigma k (blockBasis (.inr i))).grad
  let e := fun i => vectorWeakHaarNorm U (fun x => g i x-(blockBasis (.inr i)).2)
  let p := fun i : Fin 2 => Real.sqrt (vecDot (blockBasis (.inr i)).2 (blockBasis (.inr i)).2)
  have hp (i : Fin 2) : vectorWeakHaarNorm U (g i)≤e i+p i :=
    old_signed_vector_weak_affine_bound U (g i) (blockBasis (.inr i)).2
      (fun j => memLp_normalized_of_memL2On
        ((oldSignedCellReciprocalPotential Q U hsub nu sigma hnu hsigma k (blockBasis (.inr i))).grad_memVectorL2.eval j))
  have he (i : Fin 2) : e i=vectorWeakHaarNorm U (oldSignedPairedDefectField Q nu sigma hnu hsigma k true (.inr i)) := by
    apply old_signed_vector_weak_congr
    have hh := ae_restrict_of_ae_restrict_of_subset hsub
      (old_signed_frame_reciprocal_potential_grad Q nu sigma hnu hsigma k (blockBasis (.inr i)))
    filter_upwards [hh] with x hx
    change (oldSignedFrameReciprocalPotential Q nu sigma hnu hsigma k (blockBasis (.inr i))).grad x-_= _
    rw [hx]
    rfl
  have hpsum : (∑ i : Fin 2,p i^2)=(2:ℝ) := by
    simp [p,blockBasis,vecDot,Fin.sum_univ_two]
    norm_num
  have hecap : (∑ i : Fin 2,e i^2)≤oldHessianBottomPairedCellEnergy Q U nu sigma hnu hsigma k := by
    simp_rw [he]
    simp only [vectorWeakHaarNorm,Real.sq_sqrt (vectorWeakHaarEnergy_nonneg _ _)]
    unfold oldHessianBottomPairedCellEnergy
    rw [Fintype.sum_sum_type]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => vectorWeakHaarEnergy_nonneg U _))
  calc
    _ ≤ Real.sqrt (∑ i : Fin 2,(e i+p i)^2) := Real.sqrt_le_sqrt
      (Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (Real.sqrt_nonneg _) (hp i) 2))
    _ ≤ Real.sqrt (∑ i : Fin 2,e i^2)+Real.sqrt (∑ i : Fin 2,p i^2) := sqrt_finset_sq_add_le Finset.univ e p
    _ ≤ Real.sqrt (oldHessianBottomPairedCellEnergy Q U nu sigma hnu hsigma k)+Real.sqrt 2 := by
      rw [hpsum]
      exact add_le_add (Real.sqrt_le_sqrt hecap) le_rfl
    _ = _ := add_comm _ _

end
end ASDExplicitGamma.Scalar
