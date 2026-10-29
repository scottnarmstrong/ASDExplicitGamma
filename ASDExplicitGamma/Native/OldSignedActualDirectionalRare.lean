module

public import ASDExplicitGamma.Native.OldSignedPartialFrameHistory
public import ASDExplicitGamma.Native.OldSignedDescendantDirectionalMean
public import ASDExplicitGamma.Native.OldSignedRareTraceIntegral

/-! Correlated rare payments for the actual paired directional matrix.
Only the deterministic baseline receives the annealed half-trace factor. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Inverse Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Every depth of the actual common-tiling trace is genuinely integrable. -/
theorem old_signed_actual_trace_depth_integrable (M : ABKModel 2) (n : ℤ)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (j : ℕ) :
    Integrable (fun ω => rawWeakTraceSequence M n (originCube 2 n) t ω j)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  simp_rw [←old_signed_one_shell_trace_depth,old_signed_partial_trace_depth]
  simp only [Nat.cast_one,add_sub_cancel_right]
  unfold descendantsAverage
  dsimp only
  exact (integrable_finsetSum _ (fun U _ =>
    old_signed_trace_sample_integrable M n t ht U (Annealed.sigmaBar M n))).const_mul _

end
end ASDExplicitGamma.Native
