module

public import ASDExplicitGamma.Native.OldSignedAffineCorrectorBounds
public import ASDExplicitGamma.Native.OldSignedFlatProjection
public import ASDExplicitGamma.Cold.CoarseGramDefect
public import ASDExplicitGamma.Cold.PositiveTraceNorm
public import ASDExplicitGamma.Cold.SquareResponseOrder

/-! The affine reciprocal corrector for the actual OLD weighted minimizer. -/
@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Response Scalar Triadic Variational
open scoped BigOperators RealInnerProductSpace
open Matrix

noncomputable section

private theorem old_signed_blockMatrix_opNorm_eq_euclidean (A : BlockMat 2) :
    ‖HilbertBlockVec.applyBlockMat A‖ =
      ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (toFullBlockMat A)‖ := by
  let T := Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) (toFullBlockMat A)
  let B := HilbertBlockVec.applyBlockMat A
  have hfullSq (Y : BlockVec 2) :
      ‖(WithLp.toLp 2 (toFullBlockVec Y) : EuclideanSpace ℝ (BlockCoord 2))‖ ^ 2 =
        blockVecDot Y Y := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i : BlockCoord 2, (toFullBlockVec Y i) ^ 2) = _
    rw [← dotProduct_toFullBlockVec]
    simp [dotProduct, pow_two]
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound B (norm_nonneg _) ?_
    intro X
    let P := X.toBlockVec
    let x : EuclideanSpace ℝ (BlockCoord 2) :=
      WithLp.toLp 2 (toFullBlockVec P)
    have hx : ‖x‖ = ‖X‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      change ‖(WithLp.toLp 2 (toFullBlockVec P) :
        EuclideanSpace ℝ (BlockCoord 2))‖ ^ 2 = _
      rw [hfullSq, HilbertBlockVec.norm_sq_eq_blockVecDot]
    have hTx : T x = WithLp.toLp 2
        (toFullBlockVec (blockMatVecMul A P)) := by
      simp [T, x, Matrix.toEuclideanCLM_toLp, toFullBlockVec_blockMatVecMul]
    have hY : ‖B X‖ = ‖T x‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [HilbertBlockVec.norm_sq_applyBlockMat, hTx]
      change blockVecDot (blockMatVecMul A P) (blockMatVecMul A P) = _
      rw [← hfullSq]
    calc
      ‖B X‖ = ‖T x‖ := hY
      _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
      _ = ‖T‖ * ‖X‖ := by rw [hx]
  · let X (x : EuclideanSpace ℝ (BlockCoord 2)) :=
      HilbertBlockVec.ofBlockVec (ofFullBlockVec x.ofLp)
    have hx (x : EuclideanSpace ℝ (BlockCoord 2)) : ‖X x‖ = ‖x‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [HilbertBlockVec.norm_sq_eq_blockVecDot]
      have hx' : x = (WithLp.toLp 2
          (toFullBlockVec (ofFullBlockVec x.ofLp)) :
            EuclideanSpace ℝ (BlockCoord 2)) := by
        ext i
        cases i <;> rfl
      rw [hx', hfullSq]
      simp [X, HilbertBlockVec.toBlockVec_ofBlockVec]
    have hTx (x : EuclideanSpace ℝ (BlockCoord 2)) :
        T x = (WithLp.toLp 2
          (toFullBlockVec (blockMatVecMul A (X x).toBlockVec)) :
            EuclideanSpace ℝ (BlockCoord 2)) := by
      change (WithLp.toLp 2 ((toFullBlockMat A) *ᵥ x.ofLp) :
        EuclideanSpace ℝ (BlockCoord 2)) = _
      have hxv : toFullBlockVec (ofFullBlockVec x.ofLp) = x.ofLp := by simp
      rw [← hxv, ← toFullBlockVec_blockMatVecMul]
      congr 1
    refine ContinuousLinearMap.opNorm_le_bound T (norm_nonneg _) ?_
    intro x
    have hY : ‖B (X x)‖ = ‖T x‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [HilbertBlockVec.norm_sq_applyBlockMat, hTx x]
      exact (hfullSq (blockMatVecMul A (X x).toBlockVec)).symm
    calc
      ‖T x‖ = ‖B (X x)‖ := hY.symm
      _ ≤ ‖B‖ * ‖X x‖ := B.le_opNorm _
      _ = ‖B‖ * ‖x‖ := by rw [hx]

private theorem old_signed_full_response_norm_le_of_quadratic_bound
    (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam K : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hK : 0 ≤ K)
    (hquad : ∀ P : BlockVec 2,
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P) ≤
        K * blockVecDot P P) : Scalar.fullResponseOperatorNorm Q a ≤ K := by
  let A : FullBlockMat 2 := toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)
  let E := EuclideanSpace ℝ (BlockCoord 2)
  let T : E →L[ℝ] E := Matrix.toEuclideanCLM (𝕜 := ℝ) A
  have hA : A.IsHermitian := Cold.coarse_square_full_isHermitian Q hEll
  have hT : T.toLinearMap.IsSymmetric := by
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hTpos (x : E) : 0 ≤ T.reApplyInnerSelf x := by
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, real_inner_comm,
      Cold.matrix_euclidean_inner]
    have h := (Cold.coarse_square_full_posDef Q hEll).posSemidef.dotProduct_mulVec_nonneg
      x.ofLp
    simpa [T, A] using h
  have hfullSq (P : BlockVec 2) :
      ‖(WithLp.toLp 2 (toFullBlockVec P) : E)‖ ^ 2 = blockVecDot P P := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i : BlockCoord 2, (toFullBlockVec P i) ^ 2) = _
    rw [← dotProduct_toFullBlockVec]
    simp [dotProduct, pow_two]
  have hquadratic (x : E) :
      |RCLike.re ⟪T x, x⟫| ≤ K * ‖x‖ ^ 2 := by
    by_cases hx : x = 0
    · simp [hx, hK]
    let P : BlockVec 2 := ofFullBlockVec x.ofLp
    have hxfull : (WithLp.toLp 2 (toFullBlockVec P) : E) = x := by
      ext i
      simp [P, ofFullBlockVec_toFullBlockVec]
    have hnum : T.reApplyInnerSelf x =
        blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P) := by
      rw [ContinuousLinearMap.reApplyInnerSelf_apply, real_inner_comm,
        Cold.matrix_euclidean_inner]
      change x.ofLp ⬝ᵥ A.mulVec x.ofLp = _
      rw [← congrArg (fun y : E => y.ofLp) hxfull]
      rw [← toFullBlockVec_blockMatVecMul]
      rw [dotProduct_toFullBlockVec]
    have hPnorm : blockVecDot P P = ‖x‖ ^ 2 := by
      rw [← hxfull, hfullSq]
    have hupper : T.reApplyInnerSelf x ≤ K * ‖x‖ ^ 2 := by
      rw [hnum, ← hPnorm]
      exact hquad P
    have hupper' : RCLike.re ⟪T x, x⟫ ≤ K * ‖x‖ ^ 2 := by
      simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hupper
    have hpos' : 0 ≤ RCLike.re ⟪T x, x⟫ := by
      simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hTpos x
    have habs : |RCLike.re ⟪T x, x⟫| ≤ K * ‖x‖ ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [hK, hpos', hupper']
    exact habs
  have hnormT : ‖T‖ ≤ K := by
    refine ContinuousLinearMap.opNorm_le_of_re_inner_le hK ?_
    intro x y hx hy
    trans K * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 4
    · have hpolar : ⟪T (x + y), x + y⟫ - ⟪T (x - y), x - y⟫ =
          4 * ⟪T x, y⟫ := by
        simp only [map_add, map_sub, inner_add_left, inner_add_right,
          inner_sub_left, inner_sub_right]
        have hsym : ⟪T y, x⟫ = ⟪T x, y⟫ := by
          calc
            ⟪T y, x⟫ = ⟪y, T x⟫ := hT y x
            _ = ⟪T x, y⟫ := real_inner_comm _ _
        nlinarith [hsym]
      have hplus : ⟪T (x + y), x + y⟫ ≤ K * ‖x + y‖ ^ 2 := by
        simpa using (abs_le.mp (hquadratic (x + y))).2
      have hminus : -⟪T (x - y), x - y⟫ ≤ K * ‖x - y‖ ^ 2 := by
        have hLower := (abs_le.mp (hquadratic (x - y))).1
        have hLower' : -(K * ‖x - y‖ ^ 2) ≤ ⟪T (x - y), x - y⟫ := by
          simpa using hLower
        linarith
      have hpara : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 4 := by
        rw [parallelogram_law_with_norm ℝ x y, hx, hy]
        norm_num
      have hcross : ⟪T x, y⟫ ≤ K := by
        nlinarith [hpolar, hplus, hminus, hpara]
      have hcross' : RCLike.re ⟪T x, y⟫ ≤ K := by simpa using hcross
      rw [hpara]
      nlinarith [hcross']
    · rw [parallelogram_law_with_norm ℝ x y, hx, hy]
      norm_num [hK]
  have hnormEq : ‖T‖ = Scalar.fullResponseOperatorNorm Q a := by
    calc
      ‖T‖ = ‖HilbertBlockVec.applyBlockMat
          (coarseBlockMatrix (openCubeSet Q) a)‖ := by
            change ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
              (toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a))‖ = _
            exact (old_signed_blockMatrix_opNorm_eq_euclidean
              (coarseBlockMatrix (openCubeSet Q) a)).symm
      _ = Scalar.fullResponseOperatorNorm Q a := by
        rw [Scalar.fullResponseOperatorNorm, ← cube_coarseMatrix_eq_open Q a]
  rw [← hnormEq]
  exact hnormT

private theorem old_signed_full_response_depth_max_mono (Q : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (j : ℕ) :
    Scalar.fullResponseDepthMax Q a j ≤ Scalar.fullResponseDepthMax Q a (j + 1) := by
  unfold Scalar.fullResponseDepthMax
  apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty Q j)
  intro R hR
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hEllR := hEll.mono (measurableSet_openCubeSet R) hsub
  let f := fun S : TriadicCube 2 => Scalar.fullResponseOperatorNorm S a
  let K := Scalar.fullResponseDepthMax Q a (j + 1)
  have hK : 0 ≤ K := Scalar.full_response_depth_max_nonneg Q a (j + 1)
  have hchild (S : TriadicCube 2) (hS : S ∈ descendantsAtDepth R 1) :
      Scalar.fullResponseOperatorNorm S a ≤ K := by
    exact Scalar.full_response_norm_le_depth_max Q S a (j + 1)
      (mem_descendantsAtDepth_add hR hS)
  have hquad (P : BlockVec 2) :
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) P) ≤
        K * blockVecDot P P := by
    let q (S : TriadicCube 2) : ℝ :=
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet S) a) P)
    have hsubmat := Variational.cube_coarse_matrix_subadditive R 1 a hEllR
    have hsubquad := hsubmat P
    have havg := blockVecDot_blockMatVecMul_descendantsAverageBlockMat R 1
      (fun S => coarseBlockMatrix (openCubeSet S) a) P P
    have hchildren : descendantsAverage R 1 (fun S =>
        blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet S) a) P)) ≤
          K * blockVecDot P P := by
      have hchildren' := descendantsAverage_le (Q := R) (j := 1)
        (F := q) (H := fun _ => K * blockVecDot P P) (by
          intro S hS
          have hnorm := Scalar.block_quadratic_le_operator_norm
            (coarseBlockMatrix (openCubeSet S) a) P
          have hnorm' : q S ≤ Scalar.fullResponseOperatorNorm S a * blockVecDot P P := by
            simpa [q, Scalar.fullResponseOperatorNorm,
              ← cube_coarseMatrix_eq_open S a] using hnorm
          have hnormK := mul_le_mul_of_nonneg_right (hchild S hS)
            (blockVecDot_nonneg P)
          exact hnorm'.trans hnormK)
      simpa only [q, descendantsAverage_const] using hchildren'
    have hparent : (1 / 2 : ℝ) *
        blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) P) ≤
          (1 / 2 : ℝ) * descendantsAverage R 1 (fun S =>
            blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet S) a) P)) := by
      simpa only [havg] using hsubquad
    have hparent' : blockVecDot P
        (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) P) ≤
          descendantsAverage R 1 (fun S =>
            blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet S) a) P)) := by
      linarith only [hparent]
    exact hparent'.trans hchildren
  exact old_signed_full_response_norm_le_of_quadratic_bound R a hEllR hK hquad

private theorem old_signed_response_history_real_sum (Q : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    oldSignedResponseHistory Q a =
      (1 - Scalar.inverseHistoryDiscount) *
        (∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j *
          Scalar.fullResponseDepthMax Q a j) := by
  let α := Scalar.inverseHistoryDiscount
  let b (j : ℕ) := Scalar.fullResponseDepthMax Q a j
  have hα : 0 ≤ α := Scalar.inverse_history_discount_range.1.le
  have h1α : 0 ≤ 1 - α := sub_nonneg.mpr Scalar.inverse_history_discount_range.2.le
  have hs : Summable (fun j : ℕ => α ^ j * b j) := by
    simpa [α, b] using old_signed_response_depth_series_summable Q a hEll
  have hterm : ∀ j, 0 ≤ α ^ j * b j := fun j =>
    mul_nonneg (pow_nonneg hα j) (Scalar.full_response_depth_max_nonneg Q a j)
  have hsumNonneg : 0 ≤ ∑' j : ℕ, α ^ j * b j := tsum_nonneg hterm
  have hseries : (∑' j : ℕ, ENNReal.ofReal (α ^ j * b j)) =
      ENNReal.ofReal (∑' j : ℕ, α ^ j * b j) :=
    (ENNReal.ofReal_tsum_of_nonneg hterm hs).symm
  unfold oldSignedResponseHistory Scalar.completeFullResponseHistory
  change (ENNReal.ofReal (1 - α) *
      ∑' j : ℕ, ENNReal.ofReal (α ^ j * b j)).toReal =
    (1 - α) * ∑' j : ℕ, α ^ j * b j
  rw [hseries, ← ENNReal.ofReal_mul h1α]
  simp only [ENNReal.toReal_ofReal (mul_nonneg h1α hsumNonneg)]

/-- Each discounted actual response maximum is bounded by the complete OLD
response history, using monotonicity of the genuine coarse response norms. -/
theorem old_signed_response_depth_discount_bound (Q : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (j : ℕ) :
    Scalar.inverseHistoryDiscount ^ j * Scalar.fullResponseDepthMax Q a j ≤
      oldSignedResponseHistory Q a := by
  let α := Scalar.inverseHistoryDiscount
  let b (d : ℕ) := Scalar.fullResponseDepthMax Q a d
  have hα : 0 ≤ α := Scalar.inverse_history_discount_range.1.le
  have hb0 (d : ℕ) : 0 ≤ b d := by
    exact Scalar.full_response_depth_max_nonneg Q a d
  have hstep (d : ℕ) : b d ≤ b (d + 1) := by
    exact old_signed_full_response_depth_max_mono Q a hEll d
  have hb : Monotone b := monotone_nat_of_le_succ hstep
  have hs : Summable (fun d : ℕ => α ^ d * b d) := by
    simpa [α, b] using old_signed_response_depth_series_summable Q a hEll
  have hraw := Inverse.raw_inverse_depth_discount_bound b j hb hb0 hs
  have hEq : Inverse.rawCompleteInverseHistory b = oldSignedResponseHistory Q a := by
    rw [Inverse.rawCompleteInverseHistory,
      old_signed_response_history_real_sum Q a hEll]
  simpa [α, b] using hraw.trans_eq hEq

end
end ASDExplicitGamma.Native
