module

public import ASDExplicitGamma.Main.HotCovCellBound
public import ASDExplicitGamma.Main.ELinearFlatCaps
public import ASDExplicitGamma.Native.OldSignedFlatL2Profiles

/-! MA-E-COVARIANCE, expectation step 3: the cell-mean vectors of the finite-parent flat
fields carry exactly the complete mean profile, and its cell average is paid by the flat
L2 profile (`v + B0/2` plus, `v` minus). -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native ASDExplicitGamma.Scalar
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse

noncomputable section

theorem hotCov_cubeAverage_neg (U : TriadicCube 2) (f : Vec 2 → ℝ) :
    cubeAverage U (fun x => -f x) = -cubeAverage U f := by
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure, integral_neg]

theorem hotCov_meanVec_eq_blockdot (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (plus : Bool) (U : TriadicCube 2) (n : whiteBasisIndex) (i : Fin 2) :
    vecNormSq (hotCovFlatMeanVec Q b L plus U n i) =
      blockVecDot (oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i))
        (oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i)) := by
  cases plus <;>
  simp [hotCovFlatMeanVec, hotCovFlatMean, oldSignedBlockMean, oldSignedFlatInput,
    oldSignedFlatPlusBlock, oldSignedFlatMinusBlock, oldSignedFlatCoordinate, blockVecDot,
    vecNormSq, vecDot, cubeAverage_const, hotCov_cubeAverage_neg]

theorem hotCov_mean_cell_sum_eq (Q U : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (plus : Bool) :
    ∑' n : whiteBasisIndex, ∑ i : Fin 2, vecNormSq (hotCovFlatMeanVec Q b L plus U n i) =
      oldSignedFlatMeanSize Q U b L plus ^ 2 := by
  rw [old_signed_flat_mean_size_sq]
  exact tsum_congr fun n => Finset.sum_congr rfl fun i _ =>
    hotCov_meanVec_eq_blockdot Q b L plus U n i

theorem hotCov_mean_avg_le (Q : TriadicCube 2) (d : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (plus : Bool) :
    descendantsAverage Q d (fun U => ∑' n : whiteBasisIndex, ∑ i : Fin 2,
      vecNormSq (hotCovFlatMeanVec Q b L plus U n i)) ≤
      oldSignedFlatL2Size Q Q b L plus ^ 2 := by
  calc _ = descendantsAverage Q d (fun U => oldSignedFlatMeanSize Q U b L plus ^ 2) := by
        unfold descendantsAverage
        simp only []
        congr 1
        exact Finset.sum_congr rfl fun U _ => hotCov_mean_cell_sum_eq Q U b L plus
    _ ≤ descendantsAverage Q d (fun U => oldSignedFlatL2Size Q U b L plus ^ 2) :=
        descendantsAverage_le fun U hU => pow_le_pow_left₀ (Real.sqrt_nonneg _)
          (old_signed_flat_mean_size_le_l2 Q d b L plus U hU) 2
    _ = _ := old_signed_flat_l2_size_partition Q d b L plus

/-- Both signs together: `x^2 + y^2 <= 2 b^2 + B0/2`. -/
theorem hotCov_mean_avg_both_le (Q : TriadicCube 2) (d : ℕ) (b B0 : ℝ)
    (L : {l : ℝ // 0 < l}) (hB : oldSignedFlatBoundaryEnergy Q b L ≤ B0) :
    descendantsAverage Q d (fun U => ∑' n : whiteBasisIndex, ∑ i : Fin 2,
      vecNormSq (hotCovFlatMeanVec Q b L true U n i)) +
    descendantsAverage Q d (fun U => ∑' n : whiteBasisIndex, ∑ i : Fin 2,
      vecNormSq (hotCovFlatMeanVec Q b L false U n i)) ≤ 2 * b ^ 2 + B0 / 2 := by
  have h1 := hotCov_mean_avg_le Q d b L true
  have h2 := hotCov_mean_avg_le Q d b L false
  rw [main_flat_l2_plus_root_sq_eq] at h1
  have h3 : oldSignedFlatL2Size Q Q b L false ^ 2 ≤ b ^ 2 := by
    have := main_flat_l2_minus_root_sq_le Q b L
    simpa [sq_abs] using this
  linarith

end

end ASDExplicitGamma.Main
