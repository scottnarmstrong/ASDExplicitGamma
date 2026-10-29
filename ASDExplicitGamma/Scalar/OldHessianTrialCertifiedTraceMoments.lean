module

public import ASDExplicitGamma.Scalar.OldHessianTrialWeightedSourceTrace
public import ASDExplicitGamma.Numerics.Scalar.Lower

/-! The actual global-bank/source moments are bounded by the very same
X4², X5² and L4² expressions used in the scalar certificate. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Exact linearity of the complete finite rare-power tail. -/
theorem old_hessian_rare_tail_scale (β R θ X : ℝ) (k : ℕ) :
    rareExpansionTail β R (θ*X) k=θ*rareExpansionTail β R X k := by
  unfold rareExpansionTail
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Endpoint majorization retains the full correlated rare-power tail. -/
theorem old_hessian_endpoint_trace_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ k<N,nativeInductionState M h k) (m : ℤ) (hm : m<N)
    (r : ℕ) (hr : r=4 ∨ r=5) (k : ℕ) (hk : k≤4) :
    Integrable (fun ω => oldHessianGroupedBank M m ω^k*oldHessianSourceTrace M m r ω)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldHessianGroupedBank M m ω^k*oldHessianSourceTrace M m r ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (14103/10000:ℝ)^k*((nativeSourceExactMeanCaps.getD r 0:ℚ):ℝ)+
        rareExpansionTail (14103/10000:ℝ) (5/10^24:ℝ) ((5423/2500:ℝ)/(1-19/25)) k := by
  have hh := old_hessian_actual_weighted_source_trace M h hM hg N hpast m hm r hr k hk
  have ha : 0≤((nativeSourceExactMeanCaps.getD r 0:ℚ):ℝ) := by
    rcases hr with h|h <;> subst r <;> norm_num [nativeSourceExactMeanCaps]
  have ht : 0≤rareExpansionTail (14103/10000:ℝ) (5/10^24:ℝ) ((5423/2500:ℝ)/(1-19/25)) k := by
    unfold rareExpansionTail
    apply Finset.sum_nonneg
    intro i _
    positivity
  have hc : 0≤(14103/10000:ℝ)^k*((nativeSourceExactMeanCaps.getD r 0:ℚ):ℝ)+
      rareExpansionTail (14103/10000:ℝ) (5/10^24:ℝ) ((5423/2500:ℝ)/(1-19/25)) k :=
    add_nonneg (mul_nonneg (pow_nonneg (by norm_num) k) ha) ht
  refine ⟨hh.1,hh.2.trans ?_⟩
  rw [old_hessian_rare_tail_scale]
  calc
    _ = theta M*((14103/10000:ℝ)^k*((nativeSourceExactMeanCaps.getD r 0:ℚ):ℝ)+
        rareExpansionTail (14103/10000:ℝ) (5/10^24:ℝ) ((5423/2500:ℝ)/(1-19/25)) k) := by ring
    _ ≤ 1*((14103/10000:ℝ)^k*((nativeSourceExactMeanCaps.getD r 0:ℚ):ℝ)+
        rareExpansionTail (14103/10000:ℝ) (5/10^24:ℝ) ((5423/2500:ℝ)/(1-19/25)) k) :=
      mul_le_mul_of_nonneg_right (cold_theta_le_one M hg) hc
    _ = _ := one_mul _

/-- The actual r4/r5 first moments and r4 second moment have precisely the
certified X4², X5² and L4² budgets, including the scalar grouped reserve. -/
theorem old_hessian_actual_certified_trace_moments
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ k<N,nativeInductionState M h k) (m : ℤ) (hm : m<N) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let B := oldHessianGroupedBank M m
    let T4 := oldHessianSourceTrace M m 4
    let T5 := oldHessianSourceTrace M m 5
    Integrable (fun ω => B ω*T4 ω) μ ∧
    (∫ ω,B ω*T4 ω ∂μ) ≤ Numerics.Mirror.evalReal Numerics.Scalar.scalarRealEnv Numerics.Scalar.lowerX4SquareExpr ∧
    Integrable (fun ω => B ω*T5 ω) μ ∧
    (∫ ω,B ω*T5 ω ∂μ) ≤ Numerics.Mirror.evalReal Numerics.Scalar.scalarRealEnv Numerics.Scalar.lowerX5SquareExpr ∧
    Integrable (fun ω => B ω^2*T4 ω) μ ∧
    (∫ ω,B ω^2*T4 ω ∂μ) ≤ Numerics.Mirror.evalReal Numerics.Scalar.scalarRealEnv Numerics.Scalar.lowerL4SquareExpr := by
  intro μ B T4 T5
  have h4 := old_hessian_endpoint_trace_moment M h hM hg N hpast m hm 4 (Or.inl rfl) 1 (by norm_num)
  have h5 := old_hessian_endpoint_trace_moment M h hM hg N hpast m hm 5 (Or.inr rfl) 1 (by norm_num)
  have h42 := old_hessian_endpoint_trace_moment M h hM hg N hpast m hm 4 (Or.inl rfl) 2 (by norm_num)
  simp only [pow_one] at h4 h5
  refine ⟨h4.1,h4.2.trans_eq ?_,h5.1,h5.2.trans_eq ?_,h42.1,h42.2.trans_eq ?_⟩
  all_goals norm_num [rareExpansionTail,Finset.sum_Icc_succ_top,Nat.choose,nativeSourceExactMeanCaps,
    Numerics.Mirror.evalReal,Numerics.Scalar.sc,Numerics.Scalar.lowerHistoryExpr,
    Numerics.Scalar.lowerX4SquareExpr,Numerics.Scalar.lowerX5SquareExpr,Numerics.Scalar.lowerL4SquareExpr,
    Numerics.Scalar.lowerA4Expr,Numerics.Scalar.lowerA5Expr]

end
end ASDExplicitGamma.Scalar
