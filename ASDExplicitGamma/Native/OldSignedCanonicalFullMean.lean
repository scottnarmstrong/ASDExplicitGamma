module

public import ASDExplicitGamma.Native.OldSignedCanonicalResponseSpace
public import ASDExplicitGamma.Native.OldSignedFlatProjection

/-! Both physical affine means of the actual canonical minimizer. This
uses the parent mean only and asserts no mean on a child restriction. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- The second field of the actual parent canonical minimizer has its
prescribed affine flux mean. -/
theorem old_signed_canonical_flux_mean (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) (i : Fin 2) :
    (∫ x,(oldSignedCanonicalAffineField Q a hEll P x).2 i ∂normalizedCubeMeasure Q)=P.2 i := by
  let R := (lemmaVRecoveryData (isOpenBoundedConvexDomain_openCubeSet Q)).toMuCorrectionSpaceRecoveryData
  have hvol : (volume (openCubeSet Q)).toReal≠0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  have hm := R.recoveredField_average_state_of_isSobolevRegularDomain
    (scalarCellSystem Q a hEll) (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain hvol P
  have ht := congrArg (fun z : BlockVec 2 => z.2 i) hm
  have hi : (∫ x,(oldSignedCanonicalAffineField Q a hEll P x).2 i ∂normalizedCubeMeasure Q)=
      volumeAverage (openCubeSet Q) (fun x => (scalarCellResponseTest Q a hEll P).flux x i) := by
    rw [integral_normalized_eq_open,volumeAverage,volume_openCubeSet_toReal]
    congr 1
    apply integral_congr_ae
    filter_upwards [old_signed_canonical_affine_field_recovery Q a hEll P] with x hx
    exact congrArg (fun z : BlockVec 2 => z.2 i) hx
  exact hi.trans ht

/-- The complete parent block mean is its affine datum. -/
theorem old_signed_canonical_block_mean (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    oldSignedBlockMean Q (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)=P := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  apply Prod.ext
  · funext i
    change cubeAverage Q (fun x => (oldSignedCanonicalAffineField Q a hEll P x).1 i)=P.1 i
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    exact old_signed_canonical_primal_mean Q a hEll P i
  · funext i
    change cubeAverage Q (fun x => (oldSignedCanonicalAffineField Q a hEll P x).2 i)=P.2 i
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    exact old_signed_canonical_flux_mean Q a hEll P i

end
end ASDExplicitGamma.Native
