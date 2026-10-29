module

public import ASDExplicitGamma.Scalar.OldHessianTrialPrincipalPairing

/-! The leading frozen affine contraction uses the actual local top map.
Only the genuine global parent reciprocal gradients are cancelled. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section

/-- Coordinate integrability of the actual reciprocal coefficient action. -/
theorem old_hessian_reciprocal_field_memLp (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) (i : Fin 2) :
    MemLp (fun x => (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k) F x).2 i)
      2 (normalizedCubeMeasure Q) :=
  memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2
    (memVectorL2_snd_of_memBlockL2 (scalar_coefficient_flux_memL2 Q _
      (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
        nu sigma hnu hsigma k) hF)) i)

/-- The spatial quarter-turn form of the genuine parent cancellation. -/
theorem old_hessian_parent_reciprocal_nodal_zero (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (u : H10Function (openCubeSet Q)) :
    cubeAverage Q (fun x => vecDot (planarQuarterTurn
      (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P) x).2)
      ((diagInterpolant Q fine u.toH1Function).grad x))=0 := by
  have hJ (p : Vec 2) : matVecMul responsePlanarJ p=planarQuarterTurn p := by
    funext i
    fin_cases i <;> simp [matVecMul,responsePlanarJ,planarQuarterTurn,Fin.sum_univ_two]
  have hh := old_hessian_actual_nodal_parent_cancel Q fine nu sigma hnu hsigma k P u
  dsimp only at hh
  simp_rw [hJ] at hh
  rw [cubeAverage_eq_integralAverage_openCubeSet]
  convert hh using 1
  apply congrArg (volumeAverage (openCubeSet Q))
  funext x
  exact vecDot_comm _ _

/-- The actual local top receiver, with its fine interfaces retained, has
the same half-trace principal payment after the global parent cancellation. -/
theorem old_hessian_actual_local_principal_half (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let u := oldHessianMixedPotential Q coarse nu sigma hnu hsigma k
    let a := responseFramePlanarCoefficientField nu sigma k
    let G := fun i : Fin 2 => fun x => (scalarCoefficientFlux a
      (oldSignedLocalResidual Q (coarse+1) nu sigma hnu hsigma k
        (fun _ => (basisVec i,0)) (memLp_const (basisVec i,0))) x).2
    |∑ i : Fin 2,cubeAverage Q (fun x => vecDot (oldHessianRotatedReceiver G i x)
      ((diagInterpolant Q (coarse+1) (u i).toH1Function).grad x))| ≤
      oldHessianFineInverseHistory Q (coarse+1) nu sigma k*
        descendantsAverage Q (coarse+1) (fun U =>
          traceDefect (openCubeSet U) a 1)/2 := by
  intro u a G
  let F := fun i : Fin 2 => fun x => (scalarCoefficientFlux a
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (basisVec i,0)) x).2
  have hF (i j : Fin 2) : MemLp (fun x => F i x j) 2 (normalizedCubeMeasure Q) :=
    old_hessian_reciprocal_field_memLp Q nu sigma hnu hsigma k _ (Lp.memLp _) j
  have hG (i j : Fin 2) : MemLp (fun x => G i x j) 2 (normalizedCubeMeasure Q) :=
    old_hessian_reciprocal_field_memLp Q nu sigma hnu hsigma k _
      (old_signed_local_residual_memLp Q (coarse+1) nu sigma hnu hsigma k _ _) j
  have hRF := old_hessian_rotated_receiver_memLp Q F hF
  have hRG := old_hessian_rotated_receiver_memLp Q G hG
  have hzero (i : Fin 2) : cubeAverage Q (fun x => vecDot (oldHessianRotatedReceiver F i x)
      ((diagInterpolant Q (coarse+1) (u i).toH1Function).grad x))=0 := by
    fin_cases i
    · exact old_hessian_parent_reciprocal_nodal_zero Q (coarse+1) nu sigma hnu hsigma k
        (basisVec 1,0) (u 0)
    · change cubeAverage Q (fun x => vecDot (-planarQuarterTurn (F 0 x))
        ((diagInterpolant Q (coarse+1) (u 1).toH1Function).grad x))=0
      have hz := old_hessian_parent_reciprocal_nodal_zero Q (coarse+1) nu sigma hnu hsigma k
        (basisVec 0,0) (u 1)
      simpa only [vecDot_neg_left,cubeAverage_eq_integral_normalizedCubeMeasure,integral_neg,neg_zero]
        using congrArg Neg.neg hz
  have hd : (fun i : Fin 2 => oldHessianPatchReciprocal Q (coarse+1) nu sigma hnu hsigma k (basisVec i,0))=
      fun i x => F i x-G i x := by
    funext i
    exact old_hessian_patch_reciprocal_difference Q (coarse+1) nu sigma hnu hsigma k (basisVec i,0)
  have hp := old_hessian_actual_principal_half Q coarse nu sigma hnu hsigma k
  dsimp only at hp
  rw [hd,old_hessian_rotated_receiver_sub] at hp
  have he : (∑ i : Fin 2,cubeAverage Q (fun x => vecDot
      (oldHessianRotatedReceiver F i x-oldHessianRotatedReceiver G i x)
      ((diagInterpolant Q (coarse+1) (u i).toH1Function).grad x)))=
      -(∑ i : Fin 2,cubeAverage Q (fun x => vecDot (oldHessianRotatedReceiver G i x)
        ((diagInterpolant Q (coarse+1) (u i).toH1Function).grad x))) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [old_hessian_vector_pairing_sub Q _ _ _ (hRF i) (hRG i)
      (diagInterpolant Q (coarse+1) (u i).toH1Function).grad_memL2_normalizedCubeMeasure,hzero i,zero_sub]
  rw [he,abs_neg] at hp
  exact hp

end
end ASDExplicitGamma.Scalar
