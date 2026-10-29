module

public import ASDExplicitGamma.Native.OldSignedAffineCorrector
public import ASDExplicitGamma.Native.OldSignedHistoryBounds
public import ASDExplicitGamma.Scalar.InverseHistoryBlocks
public import ASDExplicitGamma.Variational.AdapterAmplitude
public import ASDExplicitGamma.Variational.CubeResponse

/-! The actual lower-right coarse inverse is controlled by the full doubled
response operator, and hence its complete quarter-discount history is bounded
by the response history in the same coefficient and frame. -/
@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Response Scalar Triadic Variational
open scoped ENNReal

private theorem old_signed_lowerRight_operator_norm_le (Q : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    Book.Ch02.matrixNorm (coarseBlockMatrix (cubeSet Q) a).lowerRight ≤
      Scalar.fullResponseOperatorNorm Q a := by
  let U := openCubeSet Q
  let D : Mat 2 := (coarseBlockMatrix (cubeSet Q) a).lowerRight
  let K : ℝ := Scalar.fullResponseOperatorNorm Q a
  have hvol : 0 < (volume U).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  obtain ⟨_, hCoarse, _, _, _, _, hDpos, _⟩ :=
    exists_energyMap_coarseData (isOpenBoundedConvexDomain_openCubeSet Q) hEll hvol
  have hD : D.PosDef := by
    change (coarseBlockMatrix (cubeSet Q) a).lowerRight.PosDef
    rw [cube_coarseMatrix_eq_open]
    rw [coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hCoarse]
    exact hDpos
  have hK : 0 ≤ K := by dsimp [K]; exact norm_nonneg _
  have hquadratic (v : Vec 2) :
      vecDot v (matVecMul D v) ≤ K * vecNormSq v := by
    have h := Scalar.block_quadratic_le_operator_norm
      (coarseBlockMatrix (cubeSet Q) a) (0, v)
    simpa [D, K, Scalar.fullResponseOperatorNorm, blockVecDot, blockMatVecMul,
      vecDot, vecNormSq, matVecMul, Fin.sum_univ_two] using h
  have hOrder : Homogenization.MatLoewnerLE D (K • (1 : Mat 2)) := by
    intro v
    have hq : vecDot v (matVecMul D v) ≤ K * vecDot v v := by
      simpa [vecNormSq] using hquadratic v
    have hid : matVecMul (K • (1 : Mat 2)) v = K • v := by
      ext i
      simp [matVecMul, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    rw [hid]
    rw [vecDot_smul_right]
    change (1 / 2 : ℝ) * vecDot v (matVecMul D v) ≤
      (1 / 2 : ℝ) * (K * vecDot v v)
    nlinarith
  have hKId : Book.Ch02.matrixNorm (K • (1 : Mat 2)) = K := by
    simp [Book.Ch02.matrixNorm, map_smul, norm_smul, Real.norm_eq_abs, hK]
  calc
    Book.Ch02.matrixNorm D ≤ Book.Ch02.matrixNorm (K • (1 : Mat 2)) :=
      Book.Ch02.matrixNorm_le_of_matLoewnerLE_of_posSemidef
        hD.posSemidef (Matrix.PosSemidef.smul Matrix.PosSemidef.one hK) hOrder
    _ = K := hKId

private theorem old_signed_inverse_depth_le_response_depth (Q : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (j : ℕ) :
    lemmaVInverseDepthMax Q a j ≤ Scalar.fullResponseDepthMax Q a j := by
  unfold lemmaVInverseDepthMax Scalar.fullResponseDepthMax
  apply Book.Ch02.finsetSupReal_mono _ (descendantsAtDepth_nonempty Q j)
  intro R hR
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hEllR := hEll.mono (measurableSet_openCubeSet R) hsub
  rw [Scalar.inverse_history_lowerRight R a hEllR]
  exact old_signed_lowerRight_operator_norm_le R a hEllR

/-- The literal quarter-discounted inverse history is at most the complete
full-response history, with no change of coefficient or scalar frame. -/
theorem old_signed_inverse_history_le_response_history (Q : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    oldSignedInverseHistory Q a ≤ oldSignedResponseHistory Q a := by
  have hαpos : 0 < Scalar.inverseHistoryDiscount := Scalar.inverse_history_discount_range.1
  have hαlt : Scalar.inverseHistoryDiscount < 1 := Scalar.inverse_history_discount_range.2
  have hα : 0 ≤ Scalar.inverseHistoryDiscount := hαpos.le
  have h1α : 0 ≤ 1 - Scalar.inverseHistoryDiscount := sub_nonneg.mpr hαlt.le
  have hinvSeries : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
      lemmaVInverseDepthMax Q a j) := by
    have hq : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
    have hqInv : ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ = Scalar.inverseHistoryDiscount := by
      rw [← Scalar.inverse_history_discount_eq]
    have hs := lemmaVInverseHistory_summable Q hEll hq
    simpa only [hqInv] using hs
  have hrespSeries := old_signed_response_depth_series_summable Q a hEll
  have hterm (j : ℕ) : Scalar.inverseHistoryDiscount ^ j *
      lemmaVInverseDepthMax Q a j ≤ Scalar.inverseHistoryDiscount ^ j *
      Scalar.fullResponseDepthMax Q a j :=
    mul_le_mul_of_nonneg_left (old_signed_inverse_depth_le_response_depth Q a hEll j)
      (pow_nonneg hα j)
  have hsum := hinvSeries.tsum_le_tsum hterm hrespSeries
  have hinvNonneg : ∀ j, 0 ≤ Scalar.inverseHistoryDiscount ^ j *
      lemmaVInverseDepthMax Q a j := fun j =>
    mul_nonneg (pow_nonneg hα j) (lemmaVInverseDepthMax_nonneg Q a j)
  have hrespNonneg : ∀ j, 0 ≤ Scalar.inverseHistoryDiscount ^ j *
      Scalar.fullResponseDepthMax Q a j := fun j =>
    mul_nonneg (pow_nonneg hα j) (Scalar.full_response_depth_max_nonneg Q a j)
  have hRespOf : oldSignedResponseHistory Q a =
      (1 - Scalar.inverseHistoryDiscount) *
        (∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j * Scalar.fullResponseDepthMax Q a j) := by
    unfold oldSignedResponseHistory Scalar.completeFullResponseHistory
    have hrealTsum : 0 ≤
        ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j * Scalar.fullResponseDepthMax Q a j :=
      tsum_nonneg hrespNonneg
    rw [← ENNReal.ofReal_tsum_of_nonneg hrespNonneg hrespSeries,
      ← ENNReal.ofReal_mul h1α]
    simp only [ENNReal.toReal_ofReal (mul_nonneg h1α hrealTsum)]
  rw [show oldSignedInverseHistory Q a =
      (1 - Scalar.inverseHistoryDiscount) *
        (∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j * lemmaVInverseDepthMax Q a j) by
          simp [oldSignedInverseHistory, lemmaVInverseHistory,
            Scalar.inverse_history_discount_eq]]
  rw [hRespOf]
  exact mul_le_mul_of_nonneg_left hsum h1α

end ASDExplicitGamma.Native
