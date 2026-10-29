module

public import ASDExplicitGamma.Native.OldSignedCanonicalMean
public import ASDExplicitGamma.Native.OldSignedCellProjection

/-! Actual first potentials of the canonical affine minimizers. The
zero-trace correction is recovered from the very same L2 class used by the
signed covariance and the local trial. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Variational
noncomputable section

/-- The actual canonical affine correction is a genuine parent variation. -/
theorem old_signed_canonical_error_variation (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    ScalarVariation (openCubeSet Q) (fun x => oldSignedCanonicalAffineField Q a hEll P x-P) := by
  have ht := scalar_cell_response_test_variation Q a hEll P
  have he : (fun x => (scalarCellResponseTest Q a hEll P).eval x-P)=ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => oldSignedCanonicalAffineField Q a hEll P x-P := by
    filter_upwards [old_signed_canonical_affine_field_recovery Q a hEll P] with x hx
    rw [hx]
  exact old_signed_scalar_variation_congr_ae he ht

/-- Choose the actual canonical zero-trace first correction, without a
potential witness or source estimate supplied as a premise. -/
def oldSignedCanonicalFirstCorrector (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    H10Function (openCubeSet Q) :=
  (old_signed_canonical_error_variation Q a hEll P).2.1.choose

/-- Its gradient is exactly the first block of the actual canonical error. -/
theorem old_signed_canonical_first_corrector_grad (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    (oldSignedCanonicalFirstCorrector Q a hEll P).toH1Function.grad=
      fun x => (oldSignedCanonicalAffineField Q a hEll P x).1-P.1 :=
  (old_signed_canonical_error_variation Q a hEll P).2.1.choose_spec

/-- The actual affine first potential used in the localized OLD source. -/
def oldSignedCanonicalFirstPotential (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    H1Function (openCubeSet Q) :=
  lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1
    (oldSignedCanonicalFirstCorrector Q a hEll P)

/-- No gradient equality is assumed when constructing the local source. -/
theorem old_signed_canonical_first_potential_grad (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    (oldSignedCanonicalFirstPotential Q a hEll P).grad=
      fun x => (oldSignedCanonicalAffineField Q a hEll P x).1 := by
  funext x
  simp only [oldSignedCanonicalFirstPotential,lemmaVAffinePotential,H1Function.add_grad,
    H1Function.affineOnIsSobolevRegularDomain_grad,old_signed_canonical_first_corrector_grad]
  abel

end
end ASDExplicitGamma.Native
