module

public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedThetaTrace
public import ASDExplicitGamma.Scalar.OldHessianTrialWeakRareBudget

/-! One literal grouped weak-proxy term, with the global and local rare
products both integrated on the same original cutoff sample space. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The actual weighted depth term is integrable and retains its exact
completed source mean and both correlated scalar-grouped rare payments. -/
theorem old_hessian_grouped_theta_term_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (k : ℕ) (hk : k≤3) (j : ℕ) :
    Integrable (fun ω => oldHessianGroupedBank M m ω^k*oldHessianGroupedOldThetaTerm M m j ω)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldHessianGroupedBank M m ω^k*oldHessianGroupedOldThetaTerm M m j ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (14103/10000:ℝ)^k*mixedBridgeLocalWeight M j*inSourceMeanActual M m (5+j) 0+
        oldHessianWeakRareBudget M k j := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let B := oldHessianGroupedBank M m
  let R := oldHessianLocalDepthRare M m j
  let T := oldHessianFineDepthTrace M m j
  let w := (1-inverseHistoryDiscount^2)*inverseHistoryDiscount^(2*j)
  let b := (3683/2500:ℝ)*bankDepthFrame M j
  have hpref : 0≤1-inverseHistoryDiscount^2 := sub_nonneg.mpr
    (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  have hw : 0≤w := mul_nonneg hpref (pow_nonneg inverse_history_discount_range.1.le _)
  have hb : 0≤b := mul_nonneg (by norm_num) (bankDepthFrame_pos M j).le
  have hglobal := old_hessian_actual_grouped_real_bank M h hM hg N hpast m hm
  have hmean := old_hessian_fine_depth_trace_mean M m j
  have hglob := old_signed_rare_history_power_payment B (oldHessianGroupedRare M m) T
    (14103/10000:ℝ) (5/10^24:ℝ) (rawWeakTraceProfileEnvelope M j) k (by omega)
    (by norm_num) (by norm_num) (old_hessian_raw_profile_nonneg M j)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    (old_hessian_fine_depth_trace_nonneg M m j)
    hglobal.1.aestronglyMeasurable hglobal.2.1.aestronglyMeasurable hmean.1.aestronglyMeasurable
    hglobal.2.2.2.2 hglobal.2.2.2.1
    (old_hessian_fine_depth_trace_profile M h hM hg N hpast m hm j)
  have hloc := old_hessian_actual_correlated_depth_rare M h hM hg N hpast m hm j k hk
  have he : (fun ω => oldHessianGroupedBank M m ω^k*oldHessianGroupedOldThetaTerm M m j ω)=
      (fun ω => (w*b)*(B ω^k*T ω)+w*(B ω^k*R ω*T ω)) := by
    funext ω
    unfold oldHessianGroupedOldThetaTerm
    dsimp only [w,b,B,R,T]
    ring
  have hlocalInt : Integrable (fun ω => B ω^k*R ω*T ω) μ := hloc.1
  have hi : Integrable (fun ω => (w*b)*(B ω^k*T ω)+w*(B ω^k*R ω*T ω)) μ :=
    (hglob.1.const_mul (w*b)).add (hlocalInt.const_mul w)
  have hweight : mixedBridgeLocalWeight M j=w*b := by
    unfold mixedBridgeLocalWeight mixedBridgeOldInverseBaseline
    dsimp only [w,b,bankDepthFrame]
  refine ⟨he.symm ▸ hi,?_⟩
  rw [he,integral_add (hglob.1.const_mul (w*b)) (hlocalInt.const_mul w),integral_const_mul,integral_const_mul]
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hglob.2 (mul_nonneg hw hb))
    (mul_le_mul_of_nonneg_left hloc.2 hw)
  apply hsum.trans_eq
  rw [hmean.2,hweight]
  unfold oldHessianWeakRareBudget
  dsimp only [w,b]
  unfold rawWeakTraceProfileEnvelope
  ring

end
end ASDExplicitGamma.Scalar
