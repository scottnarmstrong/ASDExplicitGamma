module

public import ASDExplicitGamma.Variational.AdapterConstantSkew
public import ASDExplicitGamma.Variational.LemmaVSobolev
public import ASDExplicitGamma.Native.OldSignedReciprocalPotential
public import ASDExplicitGamma.Native.OldSignedTrialFields

/-! The principal scalar covariance cancels only the genuine global parent
gradient. The local reciprocal jumps remain in the patch comparison. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section

/-- Exact planar skew pairing, with the sign used in the frozen covariance. -/
theorem old_hessian_rotated_pairing_skew (p q : Vec 2) :
    vecDot p (matVecMul responsePlanarJ q) = -vecDot (matVecMul responsePlanarJ p) q := by
  simp only [vecDot,matVecMul,responsePlanarJ,Fin.sum_univ_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,zero_mul,one_mul,
    neg_mul,zero_add,add_zero]
  ring

/-- Zero parent trace cancels a global reciprocal gradient on the entire
parent square, without any claim of fine-cell boundary cancellation. -/
theorem old_hessian_global_rotated_gradient_cancel (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) (g : H1Function (openCubeSet Q)) :
    volumeAverage (openCubeSet Q) (fun x => vecDot (u.toH1Function.grad x)
      (matVecMul responsePlanarJ (g.grad x)))=0 := by
  have hs := planarJ_gradient_isSolenoidalZeroNormalTrace u g
  have he : (fun x => vecDot (u.toH1Function.grad x) (matVecMul responsePlanarJ (g.grad x)))=
      (fun x => -vecDot (matVecMul responsePlanarJ (u.toH1Function.grad x)) (g.grad x)) :=
    funext (fun x => old_hessian_rotated_pairing_skew _ _)
  unfold volumeAverage
  rw [he,integral_neg,hs,neg_zero,mul_zero]

/-- Membership in H10 concerns the same actual H1 function; uniqueness of
its weak gradient supplies the representative join for the global identity. -/
theorem old_hessian_memH10_rotated_gradient_cancel (Q : TriadicCube 2)
    (u g : H1Function (openCubeSet Q)) (hu : MemH10 (openCubeSet Q) u.toFun) :
    volumeAverage (openCubeSet Q) (fun x => vecDot (u.grad x)
      (matVecMul responsePlanarJ (g.grad x)))=0 := by
  obtain ⟨phi,hphi⟩ := hu
  have hg := lemmaV_H1_grad_eq_ae (isOpen_openCubeSet Q) hphi.symm
  apply Eq.trans _ (old_hessian_global_rotated_gradient_cancel Q phi g)
  unfold volumeAverage
  congr 1
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  rw [hx]

/-- The parent reciprocal field in the actual frozen frame is a global
gradient. Its cancellation is proved from the canonical Euler equation. -/
theorem old_hessian_actual_parent_reciprocal_cancel (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (u : H1Function (openCubeSet Q)) (hu : MemH10 (openCubeSet Q) u.toFun) :
    let a := responseFramePlanarCoefficientField nu sigma k
    volumeAverage (openCubeSet Q) (fun x => vecDot (u.grad x) (matVecMul responsePlanarJ
      (blockMatVecMul (blockCoeffField a x) (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x)).2))=0 := by
  intro a
  let ha := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  let g := oldSignedReciprocalPotential Q a ha P
  have hg := old_signed_reciprocal_potential_grad Q a ha P
  apply Eq.trans _ (old_hessian_memH10_rotated_gradient_cancel Q u g hu)
  unfold volumeAverage
  congr 1
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  rw [hx]
  rfl

/-- The original fine nodal interpolant has the zero parent trace needed
for the actual parent cancellation, supplied internally from its H10 input. -/
theorem old_hessian_actual_nodal_parent_cancel (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (u : H10Function (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    volumeAverage (openCubeSet Q) (fun x => vecDot ((diagInterpolant Q fine u.toH1Function).grad x)
      (matVecMul responsePlanarJ (blockMatVecMul (blockCoeffField a x)
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x)).2))=0 :=
  old_hessian_actual_parent_reciprocal_cancel Q nu sigma hnu hsigma k P
    (diagInterpolant Q fine u.toH1Function) (diagInterpolant_h10_memH10 Q fine u)

end
end ASDExplicitGamma.Scalar
