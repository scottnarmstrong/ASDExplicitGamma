module

public import ASDExplicitGamma.Native.OldSignedFlatCovarianceIntegral
public import ASDExplicitGamma.Native.OldSignedCanonicalFluxL2

/-! The complete bottom-load term of AN (6.3): the actual bottom coarse
block appears with its negative sign, plus the joint harmonic covariance.
No positivity assumption on the partially inserted law is used. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

/-- The actual reciprocal error on a bottom affine load. -/
def oldSignedBottomReciprocalError (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (i : Fin 2) (x : Vec 2) : Vec 2 :=
  (blockMatVecMul (blockCoeffField a x)
    (oldSignedCanonicalAffineField Q a hEll (0,basisVec i) x)).2-basisVec i

/-- The exact normalized bottom reciprocal-error mean is D-I. -/
theorem old_signed_bottom_reciprocal_error_mean (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (i k : Fin 2) :
    (∫ x,oldSignedBottomReciprocalError Q a hEll i x k ∂normalizedCubeMeasure Q)=
      (coarseBlockMatrix (openCubeSet Q) a).lowerRight k i-basisVec i k := by
  have hvol : (volume (openCubeSet Q)).toReal≠0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  have he : (∫ x,oldSignedBottomReciprocalError Q a hEll i x k ∂normalizedCubeMeasure Q)=
      volumeAverage (openCubeSet Q) (fun x => oldSignedBottomReciprocalError Q a hEll i x k) := by
    rw [integral_normalized_eq_open,volumeAverage,volume_openCubeSet_toReal]
  rw [he]
  change volumeAverage (openCubeSet Q)
    ((fun x => (blockMatVecMul (blockCoeffField a x)
      (oldSignedCanonicalAffineField Q a hEll (0,basisVec i) x)).2 k)-(fun _ => basisVec i k))=_
  rw [volumeAverage_sub (old_signed_reciprocal_coordinate_integrable Q a hEll (0,basisVec i) k)
    (integrableOn_const (volume_openCubeSet_lt_top Q).ne),volumeAverage_const hvol,
    old_signed_bottom_block_mean]

/-- Exact bottom-load AN (6.3), with the complete physical covariance sum
outside the source normalized integral and the signed inverse term retained. -/
theorem old_signed_bottom_flat_covariance (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (b : ℝ) (L : {l : ℝ // 0 < l}) :
    HasSum (fun n : whiteBasisIndex => 2*∑ i : Fin 2,∑ k : Fin 2,
      ∫ x,oldSignedBottomReciprocalError Q a hEll i x k*
        q3Convolution b L h3Zero (whiteBasis n) x*
        matVecMul responsePlanarJ (fun l => mainFlatMinusCoordinate Q b L n (i,l) x) k
          ∂normalizedCubeMeasure Q)
      (-b^2*(Matrix.trace (coarseBlockMatrix (openCubeSet Q) a).lowerRight-2)+
        2*∑ i : Fin 2,∑ k : Fin 2,∫ x,oldSignedBottomReciprocalError Q a hEll i x k*
          oldSignedRemainderCovarianceField Q b L false i x k ∂normalizedCubeMeasure Q) := by
  have hs i k := old_signed_flat_covariance_integral Q b L false i k
    (fun x => oldSignedBottomReciprocalError Q a hEll i x k)
    (old_signed_reciprocal_error_memLp Q a hEll (0,basisVec i) k)
  simp_rw [old_signed_bottom_reciprocal_error_mean] at hs
  have hh := (hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_sum (s := Finset.univ) (fun k _ => hs i k))).mul_left 2
  convert hh using 1
  · rfl
  · simp only [Fin.sum_univ_two,basisVec,Pi.single_apply,Matrix.trace,Matrix.diag]
    norm_num
    ring

end
end ASDExplicitGamma.Native
