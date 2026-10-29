module

public import ASDExplicitGamma.Native.OldSignedPairingPartition
public import ASDExplicitGamma.Native.OldSignedTopFlatCovariance
public import ASDExplicitGamma.Native.OldSignedBottomFlatCovariance

/-! Actual local beta-times-old-error feedback for both flat covariance
terms, retaining the signed inverse bulk before any absolute value. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

/-- The two-load beta on one actual cell. -/
def oldSignedCovarianceBeta (Q U : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) : ℝ :=
  Real.sqrt (∑ i : Fin 2,vectorPositiveHaarNorm U (oldSignedRemainderCovarianceField Q b L plus i)^2)

/-- The actual bottom covariance term has precisely the signed (6.3)
bulk and the local betaMinus times reciprocal-error bill. -/
theorem old_signed_bottom_covariance_feedback (Q : TriadicCube 2) (depth : ℕ)
    (a : CoeffField 2) {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (b : ℝ) (L : {l : ℝ // 0 < l}) :
    (∑' n : whiteBasisIndex,2*∑ i : Fin 2,∑ k : Fin 2,
      ∫ x,oldSignedBottomReciprocalError Q a hEll i x k*
        q3Convolution b L h3Zero (whiteBasis n) x*
        matVecMul responsePlanarJ (fun l => mainFlatMinusCoordinate Q b L n (i,l) x) k
          ∂normalizedCubeMeasure Q)≤
      -b^2*(Matrix.trace (coarseBlockMatrix (openCubeSet Q) a).lowerRight-2)+
        2*descendantsAverage Q depth (fun U => oldSignedCovarianceBeta Q U b L false*
          Real.sqrt (∑ i : Fin 2,vectorWeakHaarNorm U (oldSignedBottomReciprocalError Q a hEll i)^2)) := by
  rw [(old_signed_bottom_flat_covariance Q a hEll b L).tsum_eq]
  have hp := old_signed_covariance_partition_pairing_bound Q depth b L false
    (oldSignedBottomReciprocalError Q a hEll)
    (fun i k => old_signed_reciprocal_error_memLp Q a hEll (0,basisVec i) k)
  have hh := (le_abs_self _).trans hp
  simp only [pairing,cubeAverage_eq_integral_normalizedCubeMeasure] at hh
  have he : (fun U => Real.sqrt (∑ i : Fin 2,vectorWeakHaarNorm U
      (oldSignedBottomReciprocalError Q a hEll i)^2)*
        Real.sqrt (∑ i : Fin 2,vectorPositiveHaarNorm U
          (oldSignedRemainderCovarianceField Q b L false i)^2))=
      fun U => oldSignedCovarianceBeta Q U b L false*Real.sqrt
        (∑ i : Fin 2,vectorWeakHaarNorm U (oldSignedBottomReciprocalError Q a hEll i)^2) := by
    funext U
    exact mul_comm _ _
  rw [he] at hh
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hh (by norm_num))

/-- The top flat covariance has zero bulk, and its absolute value is
bounded by the local betaPlus times primal-error bill. -/
theorem old_signed_top_covariance_feedback (Q : TriadicCube 2) (depth : ℕ)
    (a : CoeffField 2) {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (b : ℝ) (L : {l : ℝ // 0 < l}) :
    |∑' n : whiteBasisIndex,2*∑ i : Fin 2,∑ k : Fin 2,
      ∫ x,oldSignedTopPrimalError Q a hEll i x k*
        q3Convolution b L h3Zero (whiteBasis n) x*
        matVecMul responsePlanarJ (fun l => mainFlatPlusCoordinate Q b L n (i,l) x) k
          ∂normalizedCubeMeasure Q|≤
      2*descendantsAverage Q depth (fun U => oldSignedCovarianceBeta Q U b L true*
        Real.sqrt (∑ i : Fin 2,vectorWeakHaarNorm U (oldSignedTopPrimalError Q a hEll i)^2)) := by
  rw [(old_signed_top_flat_covariance Q a hEll b L).tsum_eq,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hp := old_signed_covariance_partition_pairing_bound Q depth b L true
    (oldSignedTopPrimalError Q a hEll) (old_signed_top_primal_error_memLp Q a hEll)
  simp only [pairing,cubeAverage_eq_integral_normalizedCubeMeasure] at hp
  have he : (fun U => Real.sqrt (∑ i : Fin 2,vectorWeakHaarNorm U
      (oldSignedTopPrimalError Q a hEll i)^2)*
        Real.sqrt (∑ i : Fin 2,vectorPositiveHaarNorm U
          (oldSignedRemainderCovarianceField Q b L true i)^2))=
      fun U => oldSignedCovarianceBeta Q U b L true*Real.sqrt
        (∑ i : Fin 2,vectorWeakHaarNorm U (oldSignedTopPrimalError Q a hEll i)^2) := by
    funext U
    exact mul_comm _ _
  rw [he] at hp
  exact mul_le_mul_of_nonneg_left hp (by norm_num)

end
end ASDExplicitGamma.Native
