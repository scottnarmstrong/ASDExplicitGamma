module

public import ASDExplicitGamma.Scalar.OldHessianTrialPatchPaired

/-! The principal covariance uses one full fine trace: the coarse bottom
first fields and fine top reciprocal fields share its energy payment. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section

/-- The first component of the literal parent-minus-affine-patch field. -/
def oldHessianPatchFirst (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) : Vec 2 → Vec 2 :=
  fun x => (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x-
    oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P) x).1

/-- The reciprocal component of that same physical patch comparison. -/
def oldHessianPatchReciprocal (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) : Vec 2 → Vec 2 :=
  fun x => (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x)
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x-
      oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P) x)).2

theorem old_hessian_fine_history_nonneg (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (k : ResponseCoefficient (openCubeSet Q)) :
    0≤oldHessianFineInverseHistory Q fine nu sigma k := by
  obtain ⟨U,hU⟩ := descendantsAtDepth_nonempty Q fine
  exact (lemmaVInverseHistory_nonneg U _
    (Real.one_lt_rpow (by norm_num : (1:ℝ)<3) (by norm_num : (0:ℝ)<1/4))).trans
    (old_hessian_fine_history_le Q fine nu sigma k U hU)

/-- Coarse bottom first and fine top reciprocal fields together cost only
one complete fine trace, with no additional two-load or two-sector factor. -/
theorem old_hessian_principal_joint_weak_budget (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    (∑ i : Fin 2,lemmaVTiledWeakEnergy Q (coarse+1)
      (oldHessianPatchFirst Q coarse nu sigma hnu hsigma k (0,basisVec i)))+
    (∑ i : Fin 2,lemmaVTiledWeakEnergy Q (coarse+1)
      (oldHessianPatchReciprocal Q (coarse+1) nu sigma hnu hsigma k (basisVec i,0))) ≤
      oldHessianFineInverseHistory Q (coarse+1) nu sigma k*
        descendantsAverage Q (coarse+1) (fun U =>
          traceDefect (openCubeSet U) (responseFramePlanarCoefficientField nu sigma k) 1) := by
  let B := oldHessianFineInverseHistory Q (coarse+1) nu sigma k
  have hfirst (i : Fin 2) : lemmaVTiledWeakEnergy Q (coarse+1)
      (oldHessianPatchFirst Q coarse nu sigma hnu hsigma k (0,basisVec i)) ≤
        B*oldHessianPatchDrop Q coarse nu sigma hnu hsigma k (0,basisVec i) := by
    have hh := old_hessian_actual_patch_paired_weak Q coarse 1 nu sigma hnu hsigma k (0,basisVec i)
    have hn := lemmaVTiledWeakEnergy_nonneg Q (coarse+1)
      (oldHessianPatchReciprocal Q coarse nu sigma hnu hsigma k (0,basisVec i))
    change _+lemmaVTiledWeakEnergy Q (coarse+1)
      (oldHessianPatchReciprocal Q coarse nu sigma hnu hsigma k (0,basisVec i)) ≤ _ at hh
    exact le_trans (le_add_of_nonneg_right hn) hh
  have hrec (i : Fin 2) : lemmaVTiledWeakEnergy Q (coarse+1)
      (oldHessianPatchReciprocal Q (coarse+1) nu sigma hnu hsigma k (basisVec i,0)) ≤
        B*oldHessianPatchDrop Q (coarse+1) nu sigma hnu hsigma k (basisVec i,0) := by
    have hh := old_hessian_actual_patch_paired_weak Q (coarse+1) 0 nu sigma hnu hsigma k (basisVec i,0)
    simp only [Nat.add_zero] at hh
    have hn := lemmaVTiledWeakEnergy_nonneg Q (coarse+1)
      (oldHessianPatchFirst Q (coarse+1) nu sigma hnu hsigma k (basisVec i,0))
    change lemmaVTiledWeakEnergy Q (coarse+1)
      (oldHessianPatchFirst Q (coarse+1) nu sigma hnu hsigma k (basisVec i,0))+_ ≤ _ at hh
    exact le_trans (le_add_of_nonneg_left hn) hh
  have hs := add_le_add (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hfirst i))
    (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrec i))
  simp only [←Finset.mul_sum,←mul_add] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left
    (old_hessian_mixed_patch_trace_bound Q coarse (coarse+1) (Nat.le_add_right coarse 1)
      nu sigma hnu hsigma k) (old_hessian_fine_history_nonneg Q (coarse+1) nu sigma k))

end
end ASDExplicitGamma.Scalar
