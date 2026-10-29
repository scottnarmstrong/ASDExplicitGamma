module

public import ASDExplicitGamma.Scalar.OldHessianTrialParentWeakTheta
public import ASDExplicitGamma.Scalar.OldHessianTrialUnweightedSourceSquare
public import ASDExplicitGamma.Native.OldSignedL2ProductExpectation

/-! Correlated actual source/parent moments for the mixed derivative feedback. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
open scoped ENNReal
noncomputable section

/-- The frozen full mixed-source root coefficient is nonnegative. -/
theorem old_hessian_dmix_nonneg : 0≤evalReal scalarRealEnv lowerDmixExpr := by
  change 0≤evalReal scalarRealEnv lowerAExpr*Real.sqrt (evalReal scalarRealEnv lowerX4SquareExpr)+
    evalReal scalarRealEnv lowerColumnMixExpr*Real.sqrt (evalReal scalarRealEnv lowerXiExpr)
  have ha : 0≤evalReal scalarRealEnv lowerAExpr := by
    norm_num [evalReal,lowerAExpr,lowerS1Expr,lowerS2Expr,sc]
    positivity
  exact add_nonneg (mul_nonneg ha (Real.sqrt_nonneg _))
    (mul_nonneg (by norm_num [evalReal,lowerColumnMixExpr,sc]) (Real.sqrt_nonneg _))

/-- The repeated original bank pays beta d for the full mixed source root,
with no independence assumption and no replacement of the original law. -/
theorem old_hessian_banked_source_root_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    Integrable (fun ω => oldHessianGroupedBank M m ω*
      Real.sqrt (oldHessianSourceEnvelope M m b (q3ModelLength (m+1)) ω)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldHessianGroupedBank M m ω*
      Real.sqrt (oldHessianSourceEnvelope M m b (q3ModelLength (m+1)) ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (14103/10000:ℝ)*(|b| *evalReal scalarRealEnv lowerDmixExpr) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let B := oldHessianGroupedBank M m
  let S := oldHessianSourceEnvelope M m b (q3ModelLength (m+1))
  have hb := old_hessian_actual_grouped_real_bank M h hM hg N hpast m hm
  have h2 : eLpNorm B 2 μ≤ENNReal.ofReal (14103/10000:ℝ) :=
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (2:ℝ≥0∞)≤128)).trans hb.2.2.1
  have hB : MemLp B 2 μ := h2.trans_lt ENNReal.ofReal_lt_top
  have hbn : lpNorm B 2 μ≤(14103/10000:ℝ) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤14103/10000)] at hh
    exact hh
  have hs := old_hessian_actual_unweighted_source_square M h hM hg N hpast m hm b
  have hr := old_signed_sqrt_L2 μ S hs.1 (fun _ => sq_nonneg _)
  have hn : lpNorm (fun ω => Real.sqrt (S ω)) 2 μ≤|b| *evalReal scalarRealEnv lowerDmixExpr := by
    rw [hr.2]
    have hh := Real.sqrt_le_sqrt hs.2
    rw [Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq_eq_abs,Real.sqrt_sq old_hessian_dmix_nonneg] at hh
    exact hh
  exact old_signed_L2_product_expectation μ B _ _ _ hB hr.1 (fun _ => ENNReal.toReal_nonneg)
    (fun _ => Real.sqrt_nonneg _) (by norm_num) hbn hn

/-- The bank-weighted OLD proxy retains the exact physical parent payment;
the conservative Tparent reserve is nonnegative and is not silently discarded. -/
theorem old_hessian_banked_parent_theta_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) :
    Integrable (fun ω => oldHessianGroupedBank M m ω*oldHessianGroupedOldTheta M m ω)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldHessianGroupedBank M m ω*oldHessianGroupedOldTheta M m ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤evalReal scalarRealEnv lowerParentWeightedExpr := by
  have hh := old_hessian_grouped_old_theta_moments M h hM hg N hpast m hm 1 (by norm_num)
  simp only [pow_one] at hh
  refine ⟨hh.2.1,hh.2.2.trans ?_⟩
  have hc := mul_le_mul_of_nonneg_left (old_hessian_weak_payment_certified M hg)
    (by norm_num : (0:ℝ)≤14103/10000)
  apply hc.trans
  norm_num only [lowerParentWeightedExpr,evalReal,sc]
  exact le_add_of_nonneg_right (by norm_num)

/-- Both copies of the bank remain correlated with the actual source and
OLD parent proxy until the joint square-root Cauchy contraction. -/
theorem old_hessian_source_parent_root_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    Integrable (fun ω =>
      Real.sqrt (oldHessianGroupedBank M m ω*oldHessianSourceEnvelope M m b (q3ModelLength (m+1)) ω)*
      Real.sqrt (oldHessianGroupedBank M m ω*oldHessianGroupedOldTheta M m ω)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,Real.sqrt (oldHessianGroupedBank M m ω*oldHessianSourceEnvelope M m b (q3ModelLength (m+1)) ω)*
      Real.sqrt (oldHessianGroupedBank M m ω*oldHessianGroupedOldTheta M m ω)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      |b| *Real.sqrt (evalReal scalarRealEnv lowerSourceSquareExpr*evalReal scalarRealEnv lowerParentWeightedExpr) := by
  have hs := old_hessian_actual_source_square_certified M h hM hg N hpast m hm b
  have hgθ := old_hessian_banked_parent_theta_moment M h hM hg N hpast m hm
  have hh := old_signed_sqrt_product_expectation (Cutoff.cutoffSampleLaw M).toMeasure _ _ hs.1 hgθ.1
    (fun _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
    (fun _ => mul_nonneg ENNReal.toReal_nonneg (old_hessian_grouped_old_theta_nonneg M m _))
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hc := mul_le_mul (Real.sqrt_le_sqrt hs.2) (Real.sqrt_le_sqrt hgθ.2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hS : 0≤evalReal scalarRealEnv lowerSourceSquareExpr := by
    change 0≤_ * _
    exact mul_self_nonneg _
  rw [Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq_eq_abs,mul_assoc,←Real.sqrt_mul hS] at hc
  exact hc

end
end ASDExplicitGamma.Scalar
