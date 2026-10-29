module

public import ASDExplicitGamma.Native.ParentBoundaryBrokenSeries
public import ASDExplicitGamma.Native.OldSignedFiniteWeakTraceBound

/-! Genuine shifted complete trace proxy for broken fine-cell weak
norms of the actual parent fields. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- The shifted physical inverse-weighted trace series converges, before
its real-valued sum is used in any broken weak estimate. -/
theorem parent_boundary_broken_trace_summable (Q : TriadicCube 2) (depth : ℕ)
    (a : CoeffField 2) {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*lemmaVInverseDepthMax Q a (depth+j)*
      descendantsAverage Q (depth+j) (fun U => traceDefect (openCubeSet U) a 1)) := by
  have hs : Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*
      (lemmaVInverseDepthMax Q a j*descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1))) := by
    simpa only [mul_assoc] using old_signed_weak_trace_proxy_summable Q a hEll
  simpa only [mul_assoc] using parent_boundary_shifted_summable _ inverse_history_discount_range.1.ne'
    (fun j => lemmaVInverseDepthMax Q a j*descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)) depth hs

/-- Complete broken weak comparison from genuine depthwise projection
budgets. The right side starts at the independent comparison depth. -/
theorem parent_boundary_finite_broken_trace {I : Type*} [Fintype I]
    (Q : TriadicCube 2) (depth : ℕ) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (F : I → Vec 2 → Vec 2)
    (hF : ∀ c i,MemLp (fun x => F c x i) 2 (normalizedCubeMeasure Q))
    (hdepth : ∀ j, (∑ c : I,∑ i : Fin 2,energy Q (cubeProjection Q j (fun x => F c x i))) ≤
      lemmaVInverseDepthMax Q a j*descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)) :
    descendantsAverage Q depth (fun U => ∑ c : I,vectorWeakHaarEnergy U (F c)) ≤
      rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q a (depth+j))
        (fun j => descendantsAverage Q (depth+j) (fun U => traceDefect (openCubeSet U) a 1)) := by
  have hr := parent_boundary_broken_finite_series Q depth F hF
  have hs := parent_boundary_broken_trace_summable Q depth a hEll
  have ha := inverse_history_discount_range
  have hc : 0≤1-inverseHistoryDiscount^2 := sub_nonneg.mpr (pow_le_one₀ ha.1.le ha.2.le)
  rw [hr.2]
  apply mul_le_mul_of_nonneg_left _ hc
  apply hr.1.tsum_le_tsum _ hs
  intro j
  exact (mul_le_mul_of_nonneg_left (hdepth (depth+j)) (pow_nonneg ha.1.le (2*j))).trans_eq (by ring)

end
end ASDExplicitGamma.Native
