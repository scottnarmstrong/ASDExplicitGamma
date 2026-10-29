module

public import ASDExplicitGamma.Native.ParentBoundaryTrialTerms

/-! Canonical physical Hessians bounded by the exact nine signed trial
families, before complete-mode summation or estimation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic
noncomputable section

/-- Per physical fresh mode, the four canonical OLD Hessians are bounded
by the literal signed trial total. No covariance bound is used in this step. -/
theorem parent_boundary_canonical_hessian_le_trial_total (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) :
    (∑ c : BlockCoord 2,oldSignedPhysicalHessian Q nu sigma hnu hsigma k (blockBasis c) b L n)≤
      (parentBoundaryTrialTerms Q depth nu sigma hnu hsigma k b L).total n := by
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    parent_boundary_top_trial_expansion Q depth nu sigma hnu hsigma k b L n i)
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    parent_boundary_bottom_trial_expansion Q depth nu sigma hnu hsigma k b L n i)
  have hh := add_le_add ht hb
  have hsym (i : Fin 2) := old_signed_energy_pairing_symm Q nu sigma k
    (parentBoundaryPatchedSource Q depth nu sigma hnu hsigma k b L n (0,basisVec i))
    (oldSignedPatchedMinus Q depth nu sigma hnu hsigma k b L n i)
  simp_rw [hsym] at hh
  rw [Fintype.sum_sum_type]
  apply hh.trans_eq
  unfold OldSignedTrialTerms.total parentBoundaryTrialTerms
  simp only [oldSignedFlatInput,oldSignedFlatLoad,Bool.false_eq_true,ite_false,ite_true,
    old_signed_patched_flat_true,old_signed_patched_flat_false,Fintype.sum_sum_type]
  have hminus (i : Fin 2) : volumeAverage (openCubeSet Q) (fun x =>
      vecDot (oldSignedFlatMinusBlock Q b L n i x).2
        (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n (0,basisVec i) x).2)=0 := by
    simp [oldSignedFlatMinusBlock,vecDot,volumeAverage]
  simp only [blockBasis,basisVec] at hminus ⊢
  simp only [hminus,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_neg_distrib,
    ← Finset.mul_sum,oldSignedFlatDirichletModeEnergy]
  ring

end
end ASDExplicitGamma.Native
