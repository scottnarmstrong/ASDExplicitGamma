module

public import ASDExplicitGamma.Native.OldSignedPrimalTraceGap
public import ASDExplicitGamma.Native.OldSignedHistoryBounds
public import ASDExplicitGamma.Cold.CoarseGramDefect

/-! Finite maximum-based trace histories for the physical OLD multiplier. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational
noncomputable section

/-- The actual maximum trace at a contained descendant depth. -/
def oldSignedMaxTraceDepth (Q : TriadicCube 2) (a : CoeffField 2) (j : ℕ) : ℝ :=
  Book.Ch02.finsetSupReal (descendantsAtDepth Q j) (fun U => traceDefect (openCubeSet U) a 1)

/-- The complete normalized maximum trace history. -/
def oldSignedMaxTraceHistory (Q : TriadicCube 2) (a : CoeffField 2) : ℝ :=
  (1-inverseHistoryDiscount)*∑' j : ℕ,inverseHistoryDiscount^j*oldSignedMaxTraceDepth Q a j

/-- The trace is bounded by four times the actual Euclidean response norm. -/
theorem old_signed_trace_le_four_response (Q : TriadicCube 2) (a : CoeffField 2) :
    traceDefect (openCubeSet Q) a 1 ≤ 4*fullResponseOperatorNorm Q a := by
  have hn (c : BlockCoord 2) : blockVecDot (blockBasis c) (blockBasis c)=1 := by
    cases c <;> simp [blockBasis,blockVecDot,vecDot,Pi.single_apply]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    block_quadratic_le_operator_norm (coarseBlockMatrix (cubeSet Q) a) (blockBasis c))
  simp only [hn,mul_one,old_signed_coarse_basis_trace_sum,Finset.sum_const,Finset.card_univ,
    Fintype.card_sum,Fintype.card_fin,nsmul_eq_mul] at hh
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at hh
  simp only [traceDefect,inv_one,one_mul]
  rw [←coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q a]
  exact (sub_le_self _ (by norm_num : (0:ℝ)≤4)).trans hh

/-- Every actual maximum is nonnegative and controlled by the response maximum. -/
theorem old_signed_max_trace_depth_bounds (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (j : ℕ) :
    0 ≤ oldSignedMaxTraceDepth Q a j ∧ oldSignedMaxTraceDepth Q a j ≤ 4*fullResponseDepthMax Q a j := by
  constructor
  · exact Book.Ch02.finsetSupReal_nonneg _ _ (fun U hU =>
      Cold.coarse_square_traceDefect_nonneg U
        (hEll.mono (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)))
  · apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty Q j)
    intro U hU
    exact (old_signed_trace_le_four_response U a).trans
      (mul_le_mul_of_nonneg_left (full_response_norm_le_depth_max Q U a j hU) (by norm_num))

/-- Ellipticity supplies convergence of the maximum history itself. -/
theorem old_signed_max_trace_series_summable (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    Summable (fun j : ℕ => inverseHistoryDiscount^j*oldSignedMaxTraceDepth Q a j) := by
  have hs := (old_signed_response_depth_series_summable Q a hEll).mul_left 4
  apply Summable.of_nonneg_of_le
    (fun j => mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _) (old_signed_max_trace_depth_bounds Q a hEll j).1)
    _ hs
  intro j
  exact (mul_le_mul_of_nonneg_left (old_signed_max_trace_depth_bounds Q a hEll j).2
    (pow_nonneg inverse_history_discount_range.1.le j)).trans_eq (by ring)

/-- The real response history equals its complete summable series. -/
theorem old_signed_response_history_series (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    Summable (fun j : ℕ => inverseHistoryDiscount^j*fullResponseDepthMax Q a j) ∧
    oldSignedResponseHistory Q a=
      (1-inverseHistoryDiscount)*∑' j : ℕ,inverseHistoryDiscount^j*fullResponseDepthMax Q a j := by
  refine ⟨old_signed_response_depth_series_summable Q a hEll,?_⟩
  unfold oldSignedResponseHistory completeFullResponseHistory
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sub_nonneg.mpr inverse_history_discount_range.2.le),
    ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
    (full_response_depth_max_nonneg Q a _))]

end
end ASDExplicitGamma.Native
