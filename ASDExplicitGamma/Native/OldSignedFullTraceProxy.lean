module

public import ASDExplicitGamma.Native.OldSignedWeakTraceProxySeries
public import ASDExplicitGamma.Native.OldSignedAffineReciprocal
public import ASDExplicitGamma.Inverse.RawWeakHistory

/-! Complete full-response-weighted trace histories. All series are proved
summable before comparison or conversion from extended values. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse
noncomputable section

/-- Nonnegativity of the genuine child-average trace defect. -/
theorem old_signed_trace_depth_nonneg (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (j : ℕ) :
    0 ≤ descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1) := by
  apply descendantsAverage_nonneg
  intro U hU
  exact Cold.coarse_square_traceDefect_nonneg U
    (hEll.mono (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU))

/-- The full-response-weighted trace proxy is a genuine real series. -/
theorem old_signed_full_trace_proxy_summable (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*fullResponseDepthMax Q a j*
      descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)) := by
  have hα := inverse_history_discount_range.1.le
  have hs := (old_signed_trace_depth_series_summable Q a hEll).mul_left (oldSignedResponseHistory Q a)
  apply Summable.of_nonneg_of_le _ _ hs
  · intro j
    exact mul_nonneg (mul_nonneg (pow_nonneg hα _) (full_response_depth_max_nonneg Q a j))
      (old_signed_trace_depth_nonneg Q a hEll j)
  · intro j
    have hd := old_signed_response_depth_discount_bound Q a hEll j
    have hh := mul_le_mul_of_nonneg_right hd
      (mul_nonneg (pow_nonneg hα j) (old_signed_trace_depth_nonneg Q a hEll j))
    convert hh using 1
    rw [show 2*j=j+j by omega,pow_add]
    ring

/-- The literal extended trace history equals the complete real weak history;
its finiteness has already been established by the convergent depth series. -/
theorem old_signed_trace_history_toReal (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    rawWeakTraceHistory (fun j => descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1))=
      (oldSignedTraceHistory Q a).toReal := by
  have hα := inverse_history_discount_range
  have hc : 0 ≤ 1-inverseHistoryDiscount := sub_nonneg.mpr hα.2.le
  have hs := old_signed_trace_depth_series_summable Q a hEll
  have hn (j : ℕ) : 0 ≤ inverseHistoryDiscount^j*
      descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1) :=
    mul_nonneg (pow_nonneg hα.1.le j) (old_signed_trace_depth_nonneg Q a hEll j)
  unfold oldSignedTraceHistory rawWeakTraceHistory
  rw [←ENNReal.ofReal_tsum_of_nonneg hn hs,←ENNReal.ofReal_mul hc,
    ENNReal.toReal_ofReal (mul_nonneg hc (tsum_nonneg hn))]

/-- The complete physical full-response proxy is paid by the OLD corrector
history, retaining the exact factor `1+alpha`. -/
theorem old_signed_full_trace_proxy_le_history (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    rawWeakTraceProxy (fullResponseDepthMax Q a)
      (fun j => descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)) ≤
      oldSignedCorrectorHistory Q a := by
  have h := raw_weak_trace_proxy_le (fullResponseDepthMax Q a)
    (fun j => descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1))
    (oldSignedResponseHistory Q a) (old_signed_response_depth_discount_bound Q a hEll)
    (old_signed_trace_depth_nonneg Q a hEll) (old_signed_full_trace_proxy_summable Q a hEll)
    (old_signed_trace_depth_series_summable Q a hEll)
  rw [old_signed_trace_history_toReal Q a hEll] at h
  exact h

end
end ASDExplicitGamma.Native
