module

public import ASDExplicitGamma.Native.OldSignedCanonicalMean
public import ASDExplicitGamma.Native.OldSignedFlatCovarianceIntegral

/-! Exact top-load flat covariance cancellation. Its constant bulk is
zero for every old realization, before any annealed expectation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

/-- The actual first-gradient error on a top affine load. -/
def oldSignedTopPrimalError (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (i : Fin 2) (x : Vec 2) : Vec 2 :=
  (oldSignedCanonicalAffineField Q a hEll (basisVec i,0) x).1-basisVec i

/-- The genuine top primal errors belong to spatial L2. -/
theorem old_signed_top_primal_error_memLp (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (i k : Fin 2) :
    MemLp (fun x => oldSignedTopPrimalError Q a hEll i x k) 2 (normalizedCubeMeasure Q) := by
  have hm := memVectorL2_fst_of_memBlockL2
    (Lp.memLp (oldSignedCanonicalAffineField Q a hEll (basisVec i,0)))
  exact (hilbert_memLp_normalized_of_open Q (hm.eval k)).sub (memLp_const (basisVec i k))

/-- The top primal error has exactly zero mean, for each old realization. -/
theorem old_signed_top_primal_error_mean (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (i k : Fin 2) :
    (∫ x,oldSignedTopPrimalError Q a hEll i x k ∂normalizedCubeMeasure Q)=0 := by
  have hm := memVectorL2_fst_of_memBlockL2
    (Lp.memLp (oldSignedCanonicalAffineField Q a hEll (basisVec i,0)))
  have hi := (hilbert_memLp_normalized_of_open Q (hm.eval k)).integrable one_le_two
  change (∫ x,(oldSignedCanonicalAffineField Q a hEll (basisVec i,0) x).1 k-basisVec i k
    ∂normalizedCubeMeasure Q)=0
  rw [integral_sub hi (integrable_const _),old_signed_canonical_primal_mean]
  simp [Measure.real_def,normalizedCubeMeasure_apply_univ]

/-- Complete top-load flat covariance has only the harmonic term. Its
whole-plane constant bulk cancels exactly before taking an absolute value. -/
theorem old_signed_top_flat_covariance (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (b : ℝ) (L : {l : ℝ // 0 < l}) :
    HasSum (fun n : whiteBasisIndex => 2*∑ i : Fin 2,∑ k : Fin 2,
      ∫ x,oldSignedTopPrimalError Q a hEll i x k*
        q3Convolution b L h3Zero (whiteBasis n) x*
        matVecMul responsePlanarJ (fun l => mainFlatPlusCoordinate Q b L n (i,l) x) k
          ∂normalizedCubeMeasure Q)
      (2*∑ i : Fin 2,∑ k : Fin 2,∫ x,oldSignedTopPrimalError Q a hEll i x k*
        oldSignedRemainderCovarianceField Q b L true i x k ∂normalizedCubeMeasure Q) := by
  have hs i k := old_signed_flat_covariance_integral Q b L true i k
    (fun x => oldSignedTopPrimalError Q a hEll i x k)
    (old_signed_top_primal_error_memLp Q a hEll i k)
  simp_rw [old_signed_top_primal_error_mean,mul_zero,zero_add] at hs
  exact (hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_sum (s := Finset.univ) (fun k _ => hs i k))).mul_left 2

end
end ASDExplicitGamma.Native
