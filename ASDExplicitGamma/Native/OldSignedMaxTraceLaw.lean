module

public import ASDExplicitGamma.Native.OldSignedActualMatrixHistory
public import ASDExplicitGamma.Main.EnvelopeHMaxHistory

/-! Exact measurable carrier of the maximum trace history in the OLD panel. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- The real maximum is the physical raw maximum in the fixed completed frame. -/
theorem old_signed_actual_max_trace_depth (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    Main.mainOrdinaryTraceDepthMax M n U t j ω =
      ENNReal.ofReal (oldSignedMaxTraceDepth U (oldSignedPartialFrameField M n 1 t ω) j) := by
  classical
  let s := descendantsAtDepth U j
  let f := fun V => traceDefect (openCubeSet V) (oldSignedPartialFrameField M n 1 t ω) 1
  have hf (V : TriadicCube 2) (hV : V ∈ s) : rawCubeFourLoadTrace M n V t ω=f V := by
    unfold rawCubeFourLoadTrace f traceDefect
    rw [old_signed_source_descendant_frame M n r U hU t ω j V hV]
    simp only [frameMatrix,inv_one,one_mul,Matrix.trace_smul,smul_eq_mul]
  have hfinite : (f '' (s : Set (TriadicCube 2))).Finite := s.finite_toSet.image f
  have hne : (f '' (s : Set (TriadicCube 2))).Nonempty :=
    (descendantsAtDepth_nonempty U j).to_set.image f
  obtain ⟨V,hV,heq⟩ := hne.csSup_mem hfinite
  change s.sup (fun V => ENNReal.ofReal (rawCubeFourLoadTrace M n V t ω)) =
    ENNReal.ofReal (sSup (f '' (s : Set (TriadicCube 2))))
  apply le_antisymm
  · apply Finset.sup_le
    intro W hW
    rw [hf W hW]
    exact ENNReal.ofReal_le_ofReal (le_csSup hfinite.bddAbove ⟨W,hW,rfl⟩)
  · rw [←heq,←hf V hV]
    exact Finset.le_sup (f := fun V => ENNReal.ofReal (rawCubeFourLoadTrace M n V t ω)) hV

/-- The entire extended history is the finite real history, without a
`toReal` conversion that could discard infinity. -/
theorem old_signed_actual_max_trace_history (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    Main.mainOrdinaryTraceMaxHistory M n U t ω =
      ENNReal.ofReal (oldSignedMaxTraceHistory U (oldSignedPartialFrameField M n 1 t ω)) := by
  have hEll := (responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet (originCube 2 n)) M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 (oldSignedPartialResponseCoefficient n 1 t ω)).mono
      (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have ha : Main.mainAlpha=inverseHistoryDiscount := rfl
  unfold Main.mainOrdinaryTraceMaxHistory oldSignedMaxTraceHistory
  simp_rw [ha,old_signed_actual_max_trace_depth M n r U hU t ω,
    ←ENNReal.ofReal_mul (pow_nonneg inverse_history_discount_range.1.le _)]
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg
    (pow_nonneg inverse_history_discount_range.1.le j)
    (old_signed_max_trace_depth_bounds U (oldSignedPartialFrameField M n 1 t ω) hEll j).1)
    (old_signed_max_trace_series_summable U (oldSignedPartialFrameField M n 1 t ω) hEll),
    ←ENNReal.ofReal_mul (sub_nonneg.mpr inverse_history_discount_range.2.le)]

/-- Actual maximum histories are nonnegative before taking their laws. -/
theorem old_signed_actual_max_trace_history_nonneg (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ oldSignedMaxTraceHistory U (oldSignedPartialFrameField M n 1 t ω) := by
  have hEll := (responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet (originCube 2 n)) M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 (oldSignedPartialResponseCoefficient n 1 t ω)).mono
      (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  exact mul_nonneg (sub_nonneg.mpr inverse_history_discount_range.2.le)
    (tsum_nonneg (fun j => mul_nonneg (pow_nonneg inverse_history_discount_range.1.le j)
      (old_signed_max_trace_depth_bounds U _ hEll j).1))

/-- The physical history is finite on every sample, not merely almost surely. -/
theorem old_signed_actual_max_trace_history_finite (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    Main.mainOrdinaryTraceMaxHistory M n U t ω < ⊤ := by
  rw [old_signed_actual_max_trace_history M n r U hU t ω]
  exact ENNReal.ofReal_lt_top

end
end ASDExplicitGamma.Native
