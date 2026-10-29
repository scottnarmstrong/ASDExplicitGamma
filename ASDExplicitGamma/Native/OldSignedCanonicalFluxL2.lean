module

public import ASDExplicitGamma.Native.OldSignedCoarseMean
public import ASDExplicitGamma.Scalar.CoefficientFlux
public import ASDExplicitGamma.Triadic.HilbertHaarProjection

/-! Actual reciprocal fields of the canonical affine minimizers are L2.
This follows from the genuine coefficient operator, before using covariance
or weak-Haar estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
noncomputable section

/-- The coefficient acting on the actual affine minimizer is genuinely L2.
No reciprocal-gradient membership or moment estimate is assumed. -/
theorem old_signed_canonical_coefficient_memL2 (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    MemBlockL2 (openCubeSet Q) (fun x => blockMatVecMul (blockCoeffField a x)
      (oldSignedCanonicalAffineField Q a hEll P x)) := by
  exact scalar_coefficient_flux_memL2 Q a hEll (Lp.memLp (oldSignedCanonicalAffineField Q a hEll P))

/-- Each actual reciprocal-gradient error coordinate belongs to the
source normalized L2 space, including the bottom affine loads. -/
theorem old_signed_reciprocal_error_memLp (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (P : BlockVec 2) (k : Fin 2) :
    MemLp (fun x => (blockMatVecMul (blockCoeffField a x)
      (oldSignedCanonicalAffineField Q a hEll P x)).2 k-P.2 k) 2 (normalizedCubeMeasure Q) := by
  have hm := old_signed_canonical_coefficient_memL2 Q a hEll P
  have hc := hilbert_memLp_normalized_of_open Q ((memVectorL2_snd_of_memBlockL2 hm).eval k)
  exact hc.sub (memLp_const (P.2 k))

end
end ASDExplicitGamma.Native
