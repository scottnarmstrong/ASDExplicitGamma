module

public import ASDExplicitGamma.Scalar.OldHessianTrialPrincipalContraction
public import ASDExplicitGamma.Scalar.OldHessianTrialPrincipalCancellation

/-! Bilinearity and exact signs in the global principal pairing. All
spatial integrals are split only after genuine L2 product integrability. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section

/-- Coordinate L2 fields have an integrable actual Euclidean pairing. -/
theorem old_hessian_vector_pairing_integrable (Q : TriadicCube 2)
    (F G : Vec 2 → Vec 2)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    Integrable (fun x => vecDot (F x) (G x)) (normalizedCubeMeasure Q) := by
  unfold vecDot
  exact integrable_finsetSum _ (fun i _ => (hF i).integrable_mul (hG i))

/-- Literal field subtraction splits the normalized pairing with no
integrability premise on the product supplied by the consumer. -/
theorem old_hessian_vector_pairing_sub (Q : TriadicCube 2)
    (F G Z : Vec 2 → Vec 2)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hZ : ∀ i, MemLp (fun x => Z x i) 2 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => vecDot (F x-G x) (Z x))=
      cubeAverage Q (fun x => vecDot (F x) (Z x))-
        cubeAverage Q (fun x => vecDot (G x) (Z x)) := by
  have he (x : Vec 2) : vecDot (F x-G x) (Z x)=vecDot (F x) (Z x)-vecDot (G x) (Z x) := by
    simp only [vecDot,Pi.sub_apply,sub_mul,Finset.sum_sub_distrib]
  simp_rw [he]
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_sub (old_hessian_vector_pairing_integrable Q F Z hF hZ)
    (old_hessian_vector_pairing_integrable Q G Z hG hZ)

/-- The two exact spatial/load quarter turns commute with field subtraction. -/
theorem old_hessian_rotated_receiver_sub (F G : Fin 2 → Vec 2 → Vec 2) :
    oldHessianRotatedReceiver (fun i x => F i x-G i x)=
      fun i x => oldHessianRotatedReceiver F i x-oldHessianRotatedReceiver G i x := by
  funext i x j
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [oldHessianRotatedReceiver,planarQuarterTurn,Pi.sub_apply,Pi.neg_apply] <;> ring

/-- The unrotated reciprocal patch difference is the literal difference
of the parent and patched reciprocal fields in the same coefficient. -/
theorem old_hessian_patch_reciprocal_difference (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    oldHessianPatchReciprocal Q fine nu sigma hnu hsigma k P=
      fun x =>
        (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x)
          (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x)).2-
        (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x)
          (oldSignedLocalResidual Q fine nu sigma hnu hsigma k (fun _ => P) (memLp_const P) x)).2 := by
  funext x
  unfold oldHessianPatchReciprocal
  rw [sub_eq_add_neg,blockMatVecMul_add,
    show -(oldSignedLocalResidual Q fine nu sigma hnu hsigma k (fun _ => P) (memLp_const P) x)=
      (-1:ℝ) • oldSignedLocalResidual Q fine nu sigma hnu hsigma k (fun _ => P) (memLp_const P) x by simp,
    blockMatVecMul_smul]
  simp only [neg_one_smul,Prod.snd_add,Prod.snd_neg,sub_eq_add_neg]

end
end ASDExplicitGamma.Scalar
