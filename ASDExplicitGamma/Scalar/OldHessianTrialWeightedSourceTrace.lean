module

public import ASDExplicitGamma.Scalar.OldHessianTrialSourceTraceNorm
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedRealBank
public import ASDExplicitGamma.Native.OldSignedRarePowerPayment

/-! Correlated global-bank payments on the actual r4/r5 scalar source
trace. The grouped rare reserve is retained in every binomial term. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Every required weighted source moment is genuinely integrable. The
ordinary mean uses the certified theta-scaled row; the correlated rare tail
uses the physical strong20 cap and the full grouped reserve. -/
theorem old_hessian_actual_weighted_source_trace
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ k<N,nativeInductionState M h k) (m : ℤ) (hm : m<N)
    (r : ℕ) (hr : r=4 ∨ r=5) (k : ℕ) (hk : k≤4) :
    Integrable (fun ω => oldHessianGroupedBank M m ω^k*oldHessianSourceTrace M m r ω)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldHessianGroupedBank M m ω^k*oldHessianSourceTrace M m r ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (14103/10000:ℝ)^k*(theta M*((nativeSourceExactMeanCaps.getD r 0:ℚ):ℝ))+
        rareExpansionTail (14103/10000:ℝ) (5/10^24:ℝ)
          (theta M*((5423/2500:ℝ)/(1-19/25))) k := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let T := oldHessianSourceTrace M m r
  have hbank := old_hessian_actual_grouped_real_bank M h hM hg N hpast m hm
  have hmean := old_hessian_physical_source_mean M h hM hg N hpast m hm r hr
  have hr5 : r≤5 := by rcases hr with h|h <;> omega
  have hT20 := old_hessian_source_trace_L20 M h m (hpast m hm) r hr5
  have hT2 : eLpNorm T 2 μ≤ENNReal.ofReal (theta M*((5423/2500:ℝ)/(1-19/25))) :=
    (eLpNorm_le_eLpNorm_of_exponent_le (f := T) (μ := μ) (by norm_num : (2:ℝ≥0∞)≤20)).trans hT20
  have hTmeas : AEStronglyMeasurable T μ := hmean.1.aestronglyMeasurable
  have hp := old_signed_rare_history_power_payment (oldHessianGroupedBank M m)
    (oldHessianGroupedRare M m) T (14103/10000:ℝ) (5/10^24:ℝ)
    (theta M*((5423/2500:ℝ)/(1-19/25))) k hk (by norm_num) (by norm_num)
    (mul_nonneg (cold_theta_pos M).le (by norm_num))
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    (old_hessian_source_trace_nonneg M m r)
    hbank.1.aestronglyMeasurable hbank.2.1.aestronglyMeasurable hTmeas
    hbank.2.2.2.2 hbank.2.2.2.1 hT2
  exact ⟨hp.1,hp.2.trans (add_le_add
    (mul_le_mul_of_nonneg_left hmean.2 (pow_nonneg (by norm_num : (0:ℝ)≤14103/10000) k)) le_rfl)⟩

end
end ASDExplicitGamma.Scalar
