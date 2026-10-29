module

public import ASDExplicitGamma.Native.OldSignedCanonicalVariationPairing
public import ASDExplicitGamma.Native.OldSignedReciprocalPotential
public import ASDExplicitGamma.Variational.PairedBessel

/-! Genuine response and complementary-compatible structure of the actual
canonical parent fields, with no fictitious cell boundary conditions. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational
noncomputable section

/-- The actual canonical field as a doubled response state. -/
def oldSignedCanonicalBlockState (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (P : BlockVec 2) : BlockState 2 :=
  ⟨fun x => (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x).1,
    fun x => (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x).2⟩

/-- The same canonical representative used by AN is an actual response
state; its recovery is not assumed. -/
theorem old_signed_canonical_response_space (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (P : BlockVec 2) :
    BlockResponseSpace (responseFramePlanarCoefficientField nu sigma k) (openCubeSet Q)
      (oldSignedCanonicalBlockState Q nu sigma hnu hsigma k P) := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  let R := (lemmaVRecoveryData (isOpenBoundedConvexDomain_openCubeSet Q)).toMuCorrectionSpaceRecoveryData
  have hvol : (volume (openCubeSet Q)).toReal≠0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  have hr := R.recoveredField_mem_responseSpace_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    (scalarCellSystem Q a hEll) (isOpenBoundedConvexDomain_openCubeSet Q) hEll hvol P
  have hae := old_signed_canonical_affine_field_recovery Q a hEll P
  refine ⟨?_,?_,?_⟩
  · exact ⟨oldSignedCanonicalFirstPotential Q a hEll P,
      old_signed_canonical_first_potential_grad Q a hEll P⟩
  · intro phi
    apply Eq.trans (integral_congr_ae ?_) (hr.2.1 phi)
    filter_upwards [hae] with x hx
    exact congrArg (fun z : BlockVec 2 => vecDot z.2 (phi.toH1Function.grad x)) hx
  · intro Y hY
    apply Eq.trans (integral_congr_ae ?_) (hr.2.2 Y hY)
    filter_upwards [hae] with x hx
    exact congrArg (fun z : BlockVec 2 => blockVecDot (Y.eval x)
      (blockMatVecMul (blockCoeffField a x) z)) hx

/-- The actual canonical field is compatible, including after being used
in the parent-versus-patch comparison. -/
theorem old_signed_canonical_compatible (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    (P : BlockVec 2) :
    ScalarCompatible (openCubeSet Q) (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P) := by
  have hh := old_signed_canonical_response_space Q nu sigma hnu hsigma k P
  exact ⟨Lp.memLp _,hh.1,hh.2.1⟩

end
end ASDExplicitGamma.Native
