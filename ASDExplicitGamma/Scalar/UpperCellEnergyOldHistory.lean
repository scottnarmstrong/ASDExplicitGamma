module

public import ASDExplicitGamma.Scalar.UpperSourceCaps
public import ASDExplicitGamma.Native.OldSignedMatrixHistoryMoments

/-! The actual OLD history supplies the sensitivity matrix-majorant moment. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Measurability of the complete OLD trace history, before real conversion. -/
theorem upper_cell_old_history_measurable (M : ABKModel 2) (n : ℤ) :
    Measurable (lagTraceHistory M n 14) := by
  unfold lagTraceHistory
  exact (Measurable.tsum (fun j => (lag_trace_max_measurable M n 14 j).const_mul _)).const_mul _

/-- The accepted actual history cap implies finiteness and the real L2 cap.
No infinite history is hidden by the real conversion. -/
theorem upper_cell_old_history_L2
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (n : ℤ) (hn : n < N) :
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, lagTraceHistory M n 14 ω < ⊤) ∧
    MemLp (fun ω => (lagTraceHistory M n 14 ω).toReal) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    lpNorm (fun ω => (lagTraceHistory M n 14 ω).toReal) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ 61/10 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let H := lagTraceHistory M n 14
  have hH := upper_cell_old_history_measurable M n
  have hcap : eLpNorm H 12 μ ≤ ENNReal.ofReal (61/10:ℝ) :=
    (scalar_upper_source_caps M h hM hg N hpast n hn).2.2.2.1
  have h1 : eLpNorm H 1 μ < ⊤ :=
    ((eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1:ℝ≥0∞) ≤ 12)).trans hcap).trans_lt
      ENNReal.ofReal_lt_top
  have hlin : (∫⁻ ω,H ω ∂μ) ≠ ⊤ := by
    rw [eLpNorm_one_eq_lintegral_enorm hH.aestronglyMeasurable] at h1
    simpa using h1.ne
  have hfinite : ∀ᵐ ω ∂μ,H ω < ⊤ := ae_lt_top hH hlin
  have heq : eLpNorm (fun ω => (H ω).toReal) 2 μ = eLpNorm H 2 μ := by
    rw [← eLpNorm_ofReal _ (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))]
    exact eLpNorm_congr_ae (hfinite.mono (fun ω hω => ENNReal.ofReal_toReal hω.ne))
  have h2 : eLpNorm (fun ω => (H ω).toReal) 2 μ ≤ ENNReal.ofReal (61/10:ℝ) := by
    rw [heq]
    exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (2:ℝ≥0∞) ≤ 12)).trans hcap
  refine ⟨hfinite,h2.trans_lt ENNReal.ofReal_lt_top,?_⟩
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h2).trans_eq
    (ENNReal.toReal_ofReal (by norm_num))

/-- The literal OLD matrix majorant has the exact m used in the certified
sensitivity profile, from standing completed-state assumptions only. -/
theorem upper_cell_old_matrix_majorant_L2
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (n : ℤ) (hn : n < N) :
    let A := fun ω => 1+2*(lagTraceHistory M n 14 ω).toReal+
      Real.sqrt (2*(lagTraceHistory M n 14 ω).toReal)
    MemLp A 2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
    lpNorm A 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      1+2*(61/10:ℝ)+Real.sqrt (2*(61/10:ℝ)) := by
  have hH := upper_cell_old_history_L2 M h hM hg N hpast n hn
  exact Native.old_signed_matrix_majorant_L2 _ _ (61/10) hH.2.1
    (fun _ => ENNReal.toReal_nonneg) (by norm_num) hH.2.2

end
end ASDExplicitGamma.Scalar
