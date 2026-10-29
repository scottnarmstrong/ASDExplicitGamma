module

public import ASDExplicitGamma.Native.OldSignedCanonicalMean

/-! Actual reciprocal H1 potentials of the canonical affine minimizers,
recovered from the source Euler equation with no gradient witness assumed. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Variational
noncomputable section

/-- The actual coefficient-weighted second block is a genuine H1 gradient
almost everywhere on the parent square. -/
theorem old_signed_reciprocal_potential_exists (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    ∃ g : H1Function (openCubeSet Q),g.grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => (blockMatVecMul (blockCoeffField a x) (oldSignedCanonicalAffineField Q a hEll P x)).2 := by
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let R := (lemmaVRecoveryData hU).toMuCorrectionSpaceRecoveryData
  have hv : (volume (openCubeSet Q)).toReal≠0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  obtain ⟨g,hg⟩ := R.recoveredField_lowerImage_isPotential_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    (scalarCellSystem Q a hEll) hU hEll hv P
  refine ⟨g,?_⟩
  rw [hg]
  filter_upwards [old_signed_canonical_affine_field_recovery Q a hEll P] with x hx
  exact congrArg (fun z : BlockVec 2 => (blockMatVecMul (blockCoeffField a x) z).2) hx.symm

/-- Select the reciprocal potential from its proved source recovery. -/
def oldSignedReciprocalPotential (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    H1Function (openCubeSet Q) := (old_signed_reciprocal_potential_exists Q a hEll P).choose

/-- The chosen reciprocal potential has the actual physical second gradient. -/
theorem old_signed_reciprocal_potential_grad (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    (oldSignedReciprocalPotential Q a hEll P).grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => (blockMatVecMul (blockCoeffField a x) (oldSignedCanonicalAffineField Q a hEll P x)).2 :=
  (old_signed_reciprocal_potential_exists Q a hEll P).choose_spec

end
end ASDExplicitGamma.Native
