module

public import ASDExplicitGamma.Native.OldSignedActualLocalHistory
public import ASDExplicitGamma.Native.OldSignedQ1MatrixMoments
public import ASDExplicitGamma.Native.OldSignedL2ProductExpectation

/-! Exact correlated inverse/matrix payments for the q1 local error. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- The common bank and each cell's matrix majorant are contracted in the
same law; their product is never replaced using independence. -/
theorem old_signed_q1_inverse_matrix_product
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (r : ℕ) (hr : r=5)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0≤t ∧ t≤1) :
    let H := fun ω => oldSignedMaxTraceHistory U (oldSignedPartialFrameField M n 1 t ω)
    let A := fun ω => 1+2*H ω+Real.sqrt (2*H ω)
    let B := rawShellBandLocalHistory M n 1 t
    let C := oldSignedQ1PanelHistory t
    Integrable (fun ω => B ω*A ω) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,B ω*A ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (3683/2500:ℝ)*(1+2*C+Real.sqrt (2*C)) := by
  intro H A B C
  have hb := old_signed_actual_local_history_L2 M h hM hg n (fun l hl => hpast l hl.le) t ht
  have hm := old_signed_q1_matrix_corrector_moments M h hM hg n hpast r hr U hU t ht
  have hH0 := old_signed_actual_max_trace_history_nonneg M n r U hU t
  exact old_signed_L2_product_expectation (Cutoff.cutoffSampleLaw M).toMeasure B A _ _
    hb.1 hm.1 (fun _ => ENNReal.toReal_nonneg)
    (fun ω => add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) (hH0 ω)))
      (Real.sqrt_nonneg _)) (by norm_num) hb.2 hm.2.1

end
end ASDExplicitGamma.Native
