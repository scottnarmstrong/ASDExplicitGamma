module

public import ASDExplicitGamma.Scalar.UpperCellEnergyOldHistory
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetMatrix
public import ASDExplicitGamma.Native.OldSignedMatrixHistoryControl
public import ASDExplicitGamma.Inverse.BridgeGlobalBank

/-! Exact normalization and finite-depth maxima for the actual OLD full-matrix
history. All cubes use the same physical cutoff and the same running frame. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Variational Native Inverse
open scoped ENNReal
noncomputable section

/-- Unit-frame trace defect of the normalized cutoff is exactly the true-frame
trace defect of the physical cutoff, on every descendant cube. -/
theorem upper_cell_old_normalized_trace
    (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    traceDefect (openCubeSet Q)
      ((Annealed.sigmaBar M n:ℝ)⁻¹ • (Cutoff.coefficientCutoff M.nu n ω).toFun) 1 =
      historyTrace M n Q ω := by
  obtain ⟨Lam,hEll⟩ := cutoff_isEllipticFieldOn_cube M n ω Q
  simp only [historyTrace,traceDefect,inv_one,one_mul]
  rw [←coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q _,
    Cold.cold_coarse_frame M.nu_pos hEll (Annealed.sigmaBar M n).property]
  simp only [frameMatrix,Matrix.trace_smul,smul_eq_mul]

/-- The old real depth maximum and the actual ENNReal maximum have exactly
the same trace entries, with no loss or additional four-load factor. -/
theorem upper_cell_old_trace_depth_max
    (M : ABKModel 2) (n ell : ℤ) (j : ℕ) (ω : Cutoff.CutoffSample 2) :
    ENNReal.ofReal (oldSignedMaxTraceDepth (originCube 2 (n-ell))
      ((Annealed.sigmaBar M n:ℝ)⁻¹ • (Cutoff.coefficientCutoff M.nu n ω).toFun) j) =
      lagTraceMax M n ell j ω := by
  unfold oldSignedMaxTraceDepth
  simp_rw [upper_cell_old_normalized_trace]
  exact ennreal_finset_sup_ofReal _ (descendantsAtDepth_nonempty _ _) _

/-- Local ellipticity of the actual normalized OLD coefficient, independent
of any stochastic state bound. -/
theorem upper_cell_old_normalized_elliptic
    (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    ∃ Lam, IsEllipticFieldOn ((Annealed.sigmaBar M n:ℝ)⁻¹*M.nu) Lam (cubeSet Q)
      ((Annealed.sigmaBar M n:ℝ)⁻¹ • (Cutoff.coefficientCutoff M.nu n ω).toFun) := by
  obtain ⟨Lam,hEll⟩ := cutoff_isEllipticFieldOn_cube M n ω Q
  exact ⟨_,Cold.cold_isEllipticFieldOn_smul (inv_pos.mpr (Annealed.sigmaBar M n).property) hEll⟩

/-- The accepted extended trace history is exactly the normalized physical history. -/
theorem upper_cell_old_trace_history
    (M : ABKModel 2) (n ell : ℤ) (ω : Cutoff.CutoffSample 2) :
    lagTraceHistory M n ell ω = ENNReal.ofReal
      (oldSignedMaxTraceHistory (originCube 2 (n-ell))
        ((Annealed.sigmaBar M n:ℝ)⁻¹ • (Cutoff.coefficientCutoff M.nu n ω).toFun)) := by
  let Q := originCube 2 (n-ell)
  let a := (Annealed.sigmaBar M n:ℝ)⁻¹ • (Cutoff.coefficientCutoff M.nu n ω).toFun
  obtain ⟨Lam,hEll⟩ := upper_cell_old_normalized_elliptic M n Q ω
  have ho := hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  unfold lagTraceHistory oldSignedMaxTraceHistory
  simp_rw [Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3),
    ←upper_cell_old_trace_depth_max]
  change ENNReal.ofReal (1-inverseHistoryDiscount) *
    (∑' j : ℕ, ENNReal.ofReal (inverseHistoryDiscount^j) *
      ENNReal.ofReal (oldSignedMaxTraceDepth Q a j)) = _
  simp_rw [←ENNReal.ofReal_mul (pow_nonneg inverse_history_discount_range.1.le _)]
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg
    (pow_nonneg inverse_history_discount_range.1.le j)
    (old_signed_max_trace_depth_bounds Q a ho j).1)
    (old_signed_max_trace_series_summable Q a ho),
    ←ENNReal.ofReal_mul (sub_nonneg.mpr inverse_history_discount_range.2.le)]

/-- The real history conversion preserves the physical trace history. -/
theorem upper_cell_old_trace_history_toReal
    (M : ABKModel 2) (n ell : ℤ) (ω : Cutoff.CutoffSample 2) :
    (lagTraceHistory M n ell ω).toReal =
      oldSignedMaxTraceHistory (originCube 2 (n-ell))
        ((Annealed.sigmaBar M n:ℝ)⁻¹ • (Cutoff.coefficientCutoff M.nu n ω).toFun) := by
  obtain ⟨Lam,hEll⟩ := upper_cell_old_normalized_elliptic M n (originCube 2 (n-ell)) ω
  have ho := hEll.mono (measurableSet_openCubeSet _) (openCubeSet_subset_cubeSet _)
  rw [upper_cell_old_trace_history,ENNReal.toReal_ofReal]
  exact mul_nonneg (sub_nonneg.mpr inverse_history_discount_range.2.le)
    (tsum_nonneg (fun j => mul_nonneg (pow_nonneg inverse_history_discount_range.1.le j)
      (old_signed_max_trace_depth_bounds _ _ ho j).1))

/-- The physical OLD response history is controlled by the certified trace majorant. -/
theorem upper_cell_old_response_history_majorant
    (M : ABKModel 2) (n ell : ℤ) (ω : Cutoff.CutoffSample 2) :
    oldSignedResponseHistory (originCube 2 (n-ell))
      ((Annealed.sigmaBar M n:ℝ)⁻¹ • (Cutoff.coefficientCutoff M.nu n ω).toFun) ≤
        1+2*(lagTraceHistory M n ell ω).toReal+
          Real.sqrt (2*(lagTraceHistory M n ell ω).toReal) := by
  rw [upper_cell_old_trace_history_toReal]
  obtain ⟨Lam,hEll⟩ := upper_cell_old_normalized_elliptic M n (originCube 2 (n-ell)) ω
  exact old_signed_response_history_le_max_trace _ _
    (mul_pos (inv_pos.mpr (Annealed.sigmaBar M n).property) M.nu_pos) hEll

end
end ASDExplicitGamma.Scalar
