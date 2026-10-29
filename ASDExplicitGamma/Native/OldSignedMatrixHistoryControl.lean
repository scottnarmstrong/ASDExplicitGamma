module

public import ASDExplicitGamma.Native.OldSignedMaxTraceHistory
public import ASDExplicitGamma.Main.MultiplierMatrixBound

/-! The actual OLD matrix and corrector histories from the maximal trace history. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational
noncomputable section

/-- The finite response maximum obeys the scalar analytic trace bound. -/
theorem old_signed_response_depth_le_max_trace (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hlam : 0<lam) (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (j : ℕ) :
    fullResponseDepthMax Q a j ≤ 1+2*oldSignedMaxTraceDepth Q a j+
      Real.sqrt (2*oldSignedMaxTraceDepth Q a j) := by
  apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty Q j)
  intro U hU
  have hb := Main.main_full_response_operator_norm_le_trace_bound U hlam
    (hEll.mono (measurableSet_cubeSet U) (cubeSet_subset_of_mem_descendantsAtDepth hU))
  have ht : traceDefect (openCubeSet U) a 1 ≤ oldSignedMaxTraceDepth Q a j := by
    exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨U,hU,rfl⟩
  have he : traceDefect (cubeSet U) a 1=traceDefect (openCubeSet U) a 1 := by
    simp only [traceDefect,coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube]
  rw [he] at hb
  have h2 := mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ)≤2)
  exact hb.trans (add_le_add (add_le_add le_rfl h2) (Real.sqrt_le_sqrt h2))

/-- Reuse the generic normalized geometric matrix-history inequality.
Convergence is supplied from actual ellipticity, not assumed on the export. -/
theorem old_signed_response_history_le_max_trace (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hlam : 0<lam) (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    oldSignedResponseHistory Q a ≤ 1+2*oldSignedMaxTraceHistory Q a+
      Real.sqrt (2*oldSignedMaxTraceHistory Q a) := by
  have ho := hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  rw [(old_signed_response_history_series Q a ho).2]
  exact Main.main_weighted_matrix_history_bound inverseHistoryDiscount
    inverse_history_discount_range.1.le inverse_history_discount_range.2
    (fullResponseDepthMax Q a) (oldSignedMaxTraceDepth Q a)
    (fun j => (old_signed_max_trace_depth_bounds Q a ho j).1)
    (fun j => ⟨full_response_depth_max_nonneg Q a j,
      old_signed_response_depth_le_max_trace Q a hlam hEll j⟩)
    (old_signed_max_trace_series_summable Q a ho)

/-- The original averaged trace history is below the genuine maximum history. -/
theorem old_signed_trace_history_le_max_trace (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    (oldSignedTraceHistory Q a).toReal ≤ oldSignedMaxTraceHistory Q a := by
  have hT (j : ℕ) : 0≤descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1) := by
    apply descendantsAverage_nonneg
    intro U hU
    exact Cold.coarse_square_traceDefect_nonneg U
      (hEll.mono (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU))
  have hle (j : ℕ) : descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1) ≤
      oldSignedMaxTraceDepth Q a j := by
    rw [←descendantsAverage_const Q j (oldSignedMaxTraceDepth Q a j)]
    apply descendantsAverage_le_descendantsAverage
    intro U hU
    exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨U,hU,rfl⟩
  unfold oldSignedTraceHistory oldSignedMaxTraceHistory
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sub_nonneg.mpr inverse_history_discount_range.2.le),
    ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _) (hT _))]
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr inverse_history_discount_range.2.le)
  exact (old_signed_trace_depth_series_summable Q a hEll).tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (hle j) (pow_nonneg inverse_history_discount_range.1.le _))
    (old_signed_max_trace_series_summable Q a hEll)

/-- The actual affine corrector history has the source D*m*H control. -/
theorem old_signed_corrector_history_le_max_trace (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hlam : 0<lam) (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    oldSignedCorrectorHistory Q a ≤ (1+inverseHistoryDiscount)*
      (1+2*oldSignedMaxTraceHistory Q a+Real.sqrt (2*oldSignedMaxTraceHistory Q a))*
        oldSignedMaxTraceHistory Q a := by
  have ho := hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  have hM := old_signed_response_history_le_max_trace Q a hlam hEll
  have hT := old_signed_trace_history_le_max_trace Q a ho
  have hM0 : 0≤oldSignedResponseHistory Q a := ENNReal.toReal_nonneg
  have hD : 0≤1+inverseHistoryDiscount := add_nonneg (by norm_num) inverse_history_discount_range.1.le
  exact mul_le_mul (mul_le_mul_of_nonneg_left hM hD) hT ENNReal.toReal_nonneg
    (mul_nonneg hD (hM0.trans hM))

end
end ASDExplicitGamma.Native
