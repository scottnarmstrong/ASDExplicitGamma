module

public import ASDExplicitGamma.Native.OldSignedCoarseMean
public import ASDExplicitGamma.Triadic.PoincareCell

/-! Exact unweighted affine means of the genuine canonical minimizers,
using the actual Sobolev recovery, before any signed covariance estimate. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
noncomputable section

/-- The recovered physical affine solution represents the very same
canonical minimizer class used throughout the signed covariance proof. -/
theorem old_signed_canonical_affine_field_recovery (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    oldSignedCanonicalAffineField Q a hEll P =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (scalarCellResponseTest Q a hEll P).eval := by
  let R := (lemmaVRecoveryData (isOpenBoundedConvexDomain_openCubeSet Q)).toMuCorrectionSpaceRecoveryData
  let system := scalarCellSystem Q a hEll
  have he := R.recoveredField_minimizer_eq system P
  change toHilbertBlockL2OfBlockField (scalar_cell_response_test_memL2 Q a hEll P)=
    system.toMuHilbertRealization.minimizerMap P at he
  have hc := hilbertBlockL2ToBlockL2_toHilbertBlockL2OfBlockField
    (scalar_cell_response_test_memL2 Q a hEll P)
  rw [he] at hc
  have ht := coeFn_toBlockL2 (scalar_cell_response_test_memL2 Q a hEll P)
  rw [←hc] at ht
  exact ht

/-- The actual canonical first gradient has its affine load as exact mean. -/
theorem old_signed_canonical_primal_mean (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) (k : Fin 2) :
    (∫ x,(oldSignedCanonicalAffineField Q a hEll P x).1 k ∂normalizedCubeMeasure Q)=P.1 k := by
  let R := (lemmaVRecoveryData (isOpenBoundedConvexDomain_openCubeSet Q)).toMuCorrectionSpaceRecoveryData
  have hvol : (volume (openCubeSet Q)).toReal≠0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  have hm := R.recoveredField_average_state_of_isSobolevRegularDomain
    (scalarCellSystem Q a hEll) (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain hvol P
  have ht := congrArg (fun z : BlockVec 2 => z.1 k) hm
  have hi : (∫ x,(oldSignedCanonicalAffineField Q a hEll P x).1 k ∂normalizedCubeMeasure Q)=
      volumeAverage (openCubeSet Q) (fun x => (scalarCellResponseTest Q a hEll P).potential x k) := by
    rw [integral_normalized_eq_open,volumeAverage,volume_openCubeSet_toReal]
    congr 1
    apply integral_congr_ae
    filter_upwards [old_signed_canonical_affine_field_recovery Q a hEll P] with x hx
    exact congrArg (fun z : BlockVec 2 => z.1 k) hx
  exact hi.trans ht

end
end ASDExplicitGamma.Native
