module

public import ASDExplicitGamma.Native.ParentBoundaryCentering

/-! Exact signed centered feedback and the boundary-fixed two-load charge.
All deterministic parent means remain explicit until their Gram identification. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

/-- The parent mean of the plus contraction pairs to zero pathwise against
the actual mean-zero first-corrector gradient. -/
theorem parent_boundary_top_centered_hasSum (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    HasSum (fun n : whiteBasisIndex => 2*∑ i : Fin 2,∑ k : Fin 2,
      ∫ x,oldSignedTopPrimalError Q a hEll i x k*
        q3Convolution b L h3Zero (whiteBasis n) x*
        matVecMul responsePlanarJ (fun l => mainFlatPlusCoordinate Q b L n (i,l) x) k
          ∂normalizedCubeMeasure Q)
      (2*∑ i : Fin 2,∑ k : Fin 2,∫ x,oldSignedTopPrimalError Q a hEll i x k*
        parentBoundaryCenteredCovariance Q b L true i x k ∂normalizedCubeMeasure Q) := by
  have hs i k := parent_boundary_centered_flat_integral Q b L true i k
    (fun x => oldSignedTopPrimalError Q a hEll i x k)
    (old_signed_top_primal_error_memLp Q a hEll i k)
  simp_rw [old_signed_top_primal_error_mean,mul_zero,zero_add] at hs
  exact (hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_sum (s := Finset.univ) (fun k _ => hs i k))).mul_left 2

/-- The bottom signed feedback retains its literal deterministic parent
Gram contraction with D-I, before any absolute value. -/
theorem parent_boundary_bottom_centered_hasSum (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    HasSum (fun n : whiteBasisIndex => 2*∑ i : Fin 2,∑ k : Fin 2,
      ∫ x,oldSignedBottomReciprocalError Q a hEll i x k*
        q3Convolution b L h3Zero (whiteBasis n) x*
        matVecMul responsePlanarJ (fun l => mainFlatMinusCoordinate Q b L n (i,l) x) k
          ∂normalizedCubeMeasure Q)
      ((2*∑ i : Fin 2,∑ k : Fin 2,parentBoundaryFlatMean Q b L false i k *
          ((coarseBlockMatrix (openCubeSet Q) a).lowerRight k i-basisVec i k)) +
        2*∑ i : Fin 2,∑ k : Fin 2,∫ x,oldSignedBottomReciprocalError Q a hEll i x k*
          parentBoundaryCenteredCovariance Q b L false i x k ∂normalizedCubeMeasure Q) := by
  have hs i k := parent_boundary_centered_flat_integral Q b L false i k
    (fun x => oldSignedBottomReciprocalError Q a hEll i x k)
    (old_signed_reciprocal_error_memLp Q a hEll (0,basisVec i) k)
  simp_rw [old_signed_bottom_reciprocal_error_mean] at hs
  have hh := (hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_sum (s := Finset.univ) (fun k _ => hs i k))).mul_left 2
  simpa only [Finset.sum_add_distrib,mul_add,oldSignedFlatCoordinate,
    Bool.false_eq_true,ite_false] using hh

/-- Top boundary charge is twice the centered beta times the actual local
primal weak error, with both factors evaluated on the same fine cell. -/
theorem parent_boundary_top_centered_feedback (Q : TriadicCube 2) (depth : ℕ)
    (a : CoeffField 2) {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    |∑' n : whiteBasisIndex,2*∑ i : Fin 2,∑ k : Fin 2,
      ∫ x,oldSignedTopPrimalError Q a hEll i x k*
        q3Convolution b L h3Zero (whiteBasis n) x*
        matVecMul responsePlanarJ (fun l => mainFlatPlusCoordinate Q b L n (i,l) x) k
          ∂normalizedCubeMeasure Q| ≤
      2*descendantsAverage Q depth (fun U => parentBoundaryCenteredBeta Q U b L true *
        Real.sqrt (∑ i : Fin 2,vectorWeakHaarNorm U (oldSignedTopPrimalError Q a hEll i)^2)) := by
  rw [(parent_boundary_top_centered_hasSum Q a hEll b L).tsum_eq,abs_mul,
    abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hh := parent_boundary_centered_partition_bound Q depth b L true
    (oldSignedTopPrimalError Q a hEll) (old_signed_top_primal_error_memLp Q a hEll)
  simp only [pairing,cubeAverage_eq_integral_normalizedCubeMeasure] at hh
  exact mul_le_mul_of_nonneg_left hh (by norm_num)

/-- Bottom feedback is the signed parent Gram term plus twice the centered
beta times the actual reciprocal weak error. -/
theorem parent_boundary_bottom_centered_feedback (Q : TriadicCube 2) (depth : ℕ)
    (a : CoeffField 2) {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    (∑' n : whiteBasisIndex,2*∑ i : Fin 2,∑ k : Fin 2,
      ∫ x,oldSignedBottomReciprocalError Q a hEll i x k*
        q3Convolution b L h3Zero (whiteBasis n) x*
        matVecMul responsePlanarJ (fun l => mainFlatMinusCoordinate Q b L n (i,l) x) k
          ∂normalizedCubeMeasure Q) ≤
      (2*∑ i : Fin 2,∑ k : Fin 2,parentBoundaryFlatMean Q b L false i k *
        ((coarseBlockMatrix (openCubeSet Q) a).lowerRight k i-basisVec i k)) +
      2*descendantsAverage Q depth (fun U => parentBoundaryCenteredBeta Q U b L false *
        Real.sqrt (∑ i : Fin 2,vectorWeakHaarNorm U (oldSignedBottomReciprocalError Q a hEll i)^2)) := by
  rw [(parent_boundary_bottom_centered_hasSum Q a hEll b L).tsum_eq]
  have hh := parent_boundary_centered_partition_bound Q depth b L false
    (oldSignedBottomReciprocalError Q a hEll)
    (fun i k => old_signed_reciprocal_error_memLp Q a hEll (0,basisVec i) k)
  simp only [pairing,cubeAverage_eq_integral_normalizedCubeMeasure] at hh
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hh) (show (0:ℝ)≤2 by norm_num))

end
end ASDExplicitGamma.Native
