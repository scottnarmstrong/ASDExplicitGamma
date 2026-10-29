module

public import ASDExplicitGamma.Native.OldSignedModelTraceBridge
public import ASDExplicitGamma.Native.OldSignedQ1GeneratorCarrier
public import ASDExplicitGamma.Main.InverseObservable

/-! The actual OLD inverse-trace heat generator as the complete sum of the two
bottom-load canonical OLD Hessians on the open observation cube. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section

/-- On the open cube the canonical frame response is the coarse quadratic form. -/
theorem old_hessian_open_load_energy_quadratic (m : ℤ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (P : BlockVec 2) :
    responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 m))
      (volume_openCubeSet_originCube_toReal_pos (d := 2) m) nu sigma hnu hsigma P k =
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet (originCube 2 m))
        (responseFramePlanarCoefficientField nu sigma k)) P) := by
  let Q := originCube 2 m
  let U := openCubeSet Q
  let a := responseFramePlanarCoefficientField nu sigma k
  let hv := volume_openCubeSet_originCube_toReal_pos (d := 2) m
  have hEllO := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hE : responseFrameEnergyObservable (measurableSet_openCubeSet Q) hv nu sigma hnu hsigma P k =
      2 * Mu U P a := by
    rw [lemmaV_observable_eq_twice_muCandidate, ← lemmaV_responseSystem_eq_canonical]
    congr 1
    exact lemmaV_canonical_muCandidate_eq_Mu (isOpenBoundedConvexDomain_openCubeSet Q) hEllO hv P
  have hEll := lemmaV_frameCoefficient_isEllipticOn (measurableSet_cubeSet Q) nu sigma hnu hsigma k
  rw [hE, ← Mu_cubeSet_originCube_eq_openCubeSet,
    mu_eq_half_coarseBlockMatrix_elliptic_triCube (div_pos hnu hsigma) hEll P,
    coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
  ring

/-- The physical inverse trace is the sum of the two open bottom-load responses. -/
theorem old_hessian_inverse_observable_two_open (n : ℤ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (x : C(closure (cubeSet (originCube 2 n)),ℝ)) :
    mainInverseObservable n nu sigma x =
      ∑ i : Fin 2,responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 n))
        (volume_openCubeSet_originCube_toReal_pos (d := 2) n) nu sigma hnu hsigma (0,basisVec i)
        (pureFluxOpenResponseRestriction n x) := by
  simp_rw [old_hessian_open_load_energy_quadratic]
  rw [old_signed_open_coarse_frame n nu sigma hnu hsigma x]
  simp [mainInverseObservable,frameMatrix,Matrix.trace,Matrix.diag_apply,blockVecDot,blockMatVecMul,
    vecDot,matVecMul,Fin.sum_univ_two,basisVec]
  ring

/-- Half the inverse-trace covariance trace in the physical q3 directions is the
complete sum of the two bottom-load physical OLD Hessians. -/
theorem old_hessian_inverse_generator_physical (m : ℤ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (b : ℝ) (L : {l : ℝ // 0<l})
    (x : C(closure (cubeSet (originCube 2 m)),ℝ)) :
    (1/2:ℝ)*modelCovarianceTrace (mainInverseObservable m nu sigma)
      (pureFluxMainCubeQ3Directions m (sigma*b) L) x =
      ∑' n : whiteBasisIndex,∑ i : Fin 2,
        oldSignedPhysicalHessian (originCube 2 m) nu sigma hnu hsigma
          (pureFluxOpenResponseRestriction m x) (0,basisVec i) b L n := by
  let R := pureFluxOpenResponseRestriction m
  let E := fun i : Fin 2 => responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 m))
    (volume_openCubeSet_originCube_toReal_pos (d := 2) m) nu sigma hnu hsigma (0,basisVec i)
  let g : ResponseCoefficient (openCubeSet (originCube 2 m)) → ℝ := fun z => ∑ i,E i z
  have hd (i : Fin 2) : ContDiff ℝ 2 (E i) :=
    responseFrameEnergyObservable_contDiff _ _ nu sigma hnu hsigma _
  have hg : ContDiff ℝ 2 g := ContDiff.sum (fun i _ => hd i)
  have he : mainInverseObservable m nu sigma = fun z => g (R z) :=
    funext (fun z => old_hessian_inverse_observable_two_open m nu sigma hnu hsigma z)
  have ht : modelCovarianceTrace (mainInverseObservable m nu sigma)
      (pureFluxMainCubeQ3Directions m (sigma*b) L) x =
      modelCovarianceTrace g (pureFluxMainCubeQ3ResponseCoefficient m (sigma*b) L) (R x) := by
    rw [he]
    unfold modelCovarianceTrace
    apply tsum_congr
    intro j
    rw [old_signed_second_directional_comp_linear g hg R]
    rw [main_q3_responseCoefficient_eq_restriction]
  rw [ht]
  let f := fun H : ResponseCoefficient (openCubeSet (originCube 2 m)) =>
    (1/2:ℝ)*secondDirectionalDerivative g (R x) H
  have hf : f 0=0 := by simp [f,secondDirectionalDerivative]
  calc
    _ = ∑' j,f (pureFluxMainCubeQ3ResponseCoefficient m (sigma*b) L j) := tsum_mul_left.symm
    _ = ∑' n : whiteBasisIndex,f (pureFluxMainCubeQ3ResponseCoefficient m (sigma*b) L
        (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) n)) :=
      main_q3_directions_tsum_apply m (sigma*b) L f hf
    _ = _ := by
      apply tsum_congr
      intro n
      rw [old_signed_physical_direction_eq]
      have hs := old_signed_second_fderiv_sum_sub_const E hd 0 (R x)
        (oldSignedPhysicalCoefficient (originCube 2 m) sigma b L n)
      simp only [sub_zero] at hs
      change (1/2:ℝ)*fderiv ℝ (fun y => fderiv ℝ g y (oldSignedPhysicalCoefficient (originCube 2 m) sigma b L n))
        (R x) (oldSignedPhysicalCoefficient (originCube 2 m) sigma b L n)=_
      have hg' : g=fun y => ∑ i,E i y := rfl
      rw [hg',hs,Finset.mul_sum]
      rfl

end
end ASDExplicitGamma.Scalar
