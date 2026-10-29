module

public import ASDExplicitGamma.Native.OldSignedWeakTraceProxySeries
public import ASDExplicitGamma.Inverse.RawWeakHistory

/-! Summation of genuine paired projection budgets through all depths. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic Inverse
noncomputable section

/-- Complete weak-energy comparison for a finite family whose depth budget
has been proved. Both real series are summable before the comparison. -/
theorem old_signed_finite_weak_trace_bound {ι : Type*} [Fintype ι]
    (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (F : ι → Vec 2 → Vec 2)
    (hF : ∀ c i,MemLp (fun x => F c x i) 2 (normalizedCubeMeasure Q))
    (hdepth : ∀ j, (∑ c,∑ i,energy Q (cubeProjection Q j (fun x => F c x i))) ≤
      lemmaVInverseDepthMax Q a j*descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)) :
    (∑ c,vectorWeakHaarEnergy Q (F c)) ≤
      rawWeakTraceProxy (lemmaVInverseDepthMax Q a)
        (fun j => descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)) := by
  have hr := old_signed_finite_weak_projection_series Q F hF
  have hs := old_signed_weak_trace_proxy_summable Q a hEll
  have hα := inverse_history_discount_range
  have hc : 0 ≤ 1-inverseHistoryDiscount^2 :=
    sub_nonneg.mpr (pow_le_one₀ hα.1.le hα.2.le)
  rw [hr.2]
  apply mul_le_mul_of_nonneg_left _ hc
  apply hr.1.tsum_le_tsum _ hs
  intro j
  exact (mul_le_mul_of_nonneg_left (hdepth j) (pow_nonneg hα.1.le (2*j))).trans_eq (by ring)

end
end ASDExplicitGamma.Native
