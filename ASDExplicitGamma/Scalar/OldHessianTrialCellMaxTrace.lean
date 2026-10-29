module

public import ASDExplicitGamma.Scalar.OldHessianTrialRestrictedFrame
public import ASDExplicitGamma.Scalar.OldHessianTrialStrongTraceCap
public import ASDExplicitGamma.Native.OldSignedCellMaxHistoryMoment

/-! Actual maximum trace histories on the full OLD scalar source population. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Genuine real maximum trace history in the original large-parent medium. -/
def oldHessianCellMaxTraceHistory (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : ℝ := oldSignedMaxTraceHistory U
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient (m+129) m ω))

/-- Every actual maximum depth mark is exactly its finite extended raw
trace counterpart, with all descendants in the same physical medium. -/
theorem old_hessian_cell_max_trace_depth (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 (m+129)) 134)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    mainOrdinaryTraceDepthMax M m U 0 j ω=ENNReal.ofReal (oldSignedMaxTraceDepth U
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient (m+129) m ω)) j) := by
  classical
  let s := descendantsAtDepth U j
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
    (oldHessianOldOpenCoefficient (m+129) m ω)
  let f := fun V => traceDefect (openCubeSet V) a 1
  have hf (V : TriadicCube 2) (hV : V∈s) : rawCubeFourLoadTrace M m V 0 ω=f V :=
    (old_hessian_old_open_trace_eq M (m+129) m ω V
      ((openCubeSet_subset_of_mem_descendantsAtDepth hV).trans
        (openCubeSet_subset_of_mem_descendantsAtDepth hU))).symm
  have hfinite : (f '' (s : Set (TriadicCube 2))).Finite := s.finite_toSet.image f
  have hne : (f '' (s : Set (TriadicCube 2))).Nonempty := (descendantsAtDepth_nonempty U j).to_set.image f
  obtain ⟨V,hV,heq⟩ := hne.csSup_mem hfinite
  change s.sup (fun V => ENNReal.ofReal (rawCubeFourLoadTrace M m V 0 ω))=
    ENNReal.ofReal (sSup (f '' (s : Set (TriadicCube 2))))
  apply le_antisymm
  · apply Finset.sup_le
    intro W hW
    rw [hf W hW]
    exact ENNReal.ofReal_le_ofReal (le_csSup hfinite.bddAbove ⟨W,hW,rfl⟩)
  · rw [←heq,←hf V hV]
    exact Finset.le_sup (f := fun V => ENNReal.ofReal (rawCubeFourLoadTrace M m V 0 ω)) hV

/-- The actual real maximum history is nonnegative pointwise. -/
theorem old_hessian_cell_max_trace_nonneg (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 (m+129)) 134)
    (ω : Cutoff.CutoffSample 2) : 0≤oldHessianCellMaxTraceHistory M m U ω := by
  have hEll := (responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet (originCube 2 (m+129))) M.nu (Annealed.sigmaBar M m)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1 (oldHessianOldOpenCoefficient (m+129) m ω)).mono
      (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  exact mul_nonneg (sub_nonneg.mpr inverse_history_discount_range.2.le)
    (tsum_nonneg (fun j => mul_nonneg (pow_nonneg inverse_history_discount_range.1.le j)
      (old_signed_max_trace_depth_bounds U _ hEll j).1))

/-- Equality holds on ENNReal histories before toReal, so finiteness is
proved rather than inferred from a possibly vanishing real representative. -/
theorem old_hessian_cell_max_trace_history (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 (m+129)) 134)
    (ω : Cutoff.CutoffSample 2) :
    mainOrdinaryTraceMaxHistory M m U 0 ω=ENNReal.ofReal (oldHessianCellMaxTraceHistory M m U ω) := by
  have hEll := (responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet (originCube 2 (m+129))) M.nu (Annealed.sigmaBar M m)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1 (oldHessianOldOpenCoefficient (m+129) m ω)).mono
      (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have ha : mainAlpha=inverseHistoryDiscount := rfl
  unfold mainOrdinaryTraceMaxHistory oldHessianCellMaxTraceHistory oldSignedMaxTraceHistory
  simp_rw [ha,old_hessian_cell_max_trace_depth M m U hU ω,
    ←ENNReal.ofReal_mul (pow_nonneg inverse_history_discount_range.1.le _)]
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg
    (pow_nonneg inverse_history_discount_range.1.le j) (old_signed_max_trace_depth_bounds U _ hEll j).1)
    (old_signed_max_trace_series_summable U _ hEll),
    ←ENNReal.ofReal_mul (sub_nonneg.mpr inverse_history_discount_range.2.le)]

end
end ASDExplicitGamma.Scalar
