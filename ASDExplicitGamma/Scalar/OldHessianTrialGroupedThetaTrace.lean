module

public import ASDExplicitGamma.Scalar.OldHessianTrialCorrelatedDepthRare
public import ASDExplicitGamma.Inverse.MixedBridgeLocalBudget

/-! Literal source traces and grouped OLD weak proxy on Q_(m+129), with
the exact completed source first moments at every depth. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The actual fine common-tiling trace at additional weak depthj. -/
def oldHessianFineDepthTrace (M : ABKModel 2) (m : ℤ) (j : ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  rawWeakTraceSequence M m (originCube 2 (m+129)) 0 ω (134+j)

theorem old_hessian_fine_depth_trace_nonneg (M : ABKModel 2) (m : ℤ) (j : ℕ)
    (ω : Cutoff.CutoffSample 2) : 0≤oldHessianFineDepthTrace M m j ω :=
  raw_weak_trace_sequence_nonneg M m (originCube 2 (m+129)) 0 (by norm_num) ω (134+j)

/-- The expectation of the actual large-parent trace is exactly the
completed depth5+j source mean, with the same cutoff and true frame. -/
theorem old_hessian_fine_depth_trace_mean (M : ABKModel 2) (m : ℤ) (j : ℕ) :
    Integrable (oldHessianFineDepthTrace M m j) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldHessianFineDepthTrace M m j ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      inSourceMeanActual M m (5+j) 0 := by
  refine ⟨old_signed_source_trace_integrable M m (originCube 2 (m+129)) 0 (by norm_num) (134+j),?_⟩
  unfold oldHessianFineDepthTrace
  rw [old_signed_source_trace_mean_eq_depth M m (originCube 2 (m+129)) 0 (by norm_num) (134+j)]
  have hscale : (originCube 2 (m+129)).scale-((134+j:ℕ):ℤ)=m-((5+j:ℕ):ℤ) := by
    change m+129-((134+j:ℕ):ℤ)=_
    omega
  rw [hscale,inSourceMeanActual,modelTraceHeatAverage]
  rfl

/-- The actual fine depth traces have the complete raw profile used in
both correlated rare payments. -/
theorem old_hessian_fine_depth_trace_profile
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (j : ℕ) :
    eLpNorm (oldHessianFineDepthTrace M m j) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) :=
  old_hessian_large_parent_trace_profile M h hM hg N hpast m hm 5 (by norm_num) j

/-- Literal grouped OLD proxy on the actual fine trace population. -/
def oldHessianGroupedOldTheta (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  rawWeakTraceProxy (fun j => (3683/2500:ℝ)*bankDepthFrame M j+oldHessianLocalDepthRare M m j ω)
    (fun j => oldHessianFineDepthTrace M m j ω)

/-- Actual positive term of the complete grouped OLD proxy. -/
def oldHessianGroupedOldThetaTerm (M : ABKModel 2) (m : ℤ) (j : ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  (1-inverseHistoryDiscount^2)*inverseHistoryDiscount^(2*j)*
    ((3683/2500:ℝ)*bankDepthFrame M j+oldHessianLocalDepthRare M m j ω)*
      oldHessianFineDepthTrace M m j ω

theorem old_hessian_grouped_old_theta_term_nonneg (M : ABKModel 2) (m : ℤ) (j : ℕ)
    (ω : Cutoff.CutoffSample 2) : 0≤oldHessianGroupedOldThetaTerm M m j ω := by
  have hpref : 0≤1-inverseHistoryDiscount^2 := sub_nonneg.mpr
    (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  exact mul_nonneg (mul_nonneg (mul_nonneg hpref
    (pow_nonneg inverse_history_discount_range.1.le _))
    (add_nonneg (mul_nonneg (by norm_num) (bankDepthFrame_pos M j).le) ENNReal.toReal_nonneg))
    (old_hessian_fine_depth_trace_nonneg M m j ω)

/-- Exact series meaning; convergence is proved by the correlated moments
before the proxy enters any expected quantitative bound. -/
theorem old_hessian_grouped_old_theta_series (M : ABKModel 2) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) :
    oldHessianGroupedOldTheta M m ω=∑' j,oldHessianGroupedOldThetaTerm M m j ω := by
  unfold oldHessianGroupedOldTheta oldHessianGroupedOldThetaTerm rawWeakTraceProxy
  rw [←tsum_mul_left]
  apply tsum_congr
  intro j
  dsimp only
  ring

end
end ASDExplicitGamma.Scalar
