module

public import ASDExplicitGamma.Scalar.OldHessianTrialSourceRoot

/-! Sharp unweighted physical source-square moment. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section

/-- The first weighted coarse trace cap is precisely the frozen X4 squared. -/
theorem old_hessian_coarse_trace_cap_one :
    oldHessianCoarseTraceMomentCap 1=evalReal scalarRealEnv lowerX4SquareExpr := by
  norm_num [oldHessianCoarseTraceMomentCap,rareExpansionTail,Finset.sum_Icc_succ_top,
    Nat.choose,nativeSourceExactMeanCaps,evalReal,sc,lowerX4SquareExpr,lowerA4Expr,lowerHistoryExpr]

/-- The full source square has its unweighted d squared cap, before any
correlation with the oscillatory reciprocal receiver is contracted. -/
theorem old_hessian_actual_unweighted_source_square
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    Integrable (fun ω => oldHessianSourceEnvelope M m b (q3ModelLength (m+1)) ω) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldHessianSourceEnvelope M m b (q3ModelLength (m+1)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        b^2*(evalReal scalarRealEnv lowerDmixExpr)^2 := by
  have hh := old_hessian_actual_source_envelope_moment M h hM hg N hpast m hm b
    (q3ModelLength (m+1)) 0 (by norm_num)
  simp only [pow_zero,one_mul,Nat.reduceAdd] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  rw [old_hessian_physical_source_multiplier,old_hessian_coarse_trace_cap_one]
  have hA : 0≤evalReal scalarRealEnv lowerAExpr := by
    have ha := old_hessian_source_multiplier_nonneg (originCube 2 (m+129)) 134 1 (q3ModelLength (m+1))
    rw [old_hessian_physical_source_multiplier,abs_one,mul_one] at ha
    exact ha
  have hC := old_hessian_coarse_column_certified m b
  have hweak := old_hessian_weak_payment_certified M hg
  have hC0 : 0≤evalReal scalarRealEnv lowerColumnMixExpr*|b| := by
    norm_num [evalReal,lowerColumnMixExpr,sc]
  have hroot := mul_le_mul hC (Real.sqrt_le_sqrt hweak) (Real.sqrt_nonneg _) hC0
  have hsum := add_le_add (le_refl (evalReal scalarRealEnv lowerAExpr*|b| *
    Real.sqrt (evalReal scalarRealEnv lowerX4SquareExpr))) hroot
  have hleft : 0≤evalReal scalarRealEnv lowerAExpr*|b| *Real.sqrt (evalReal scalarRealEnv lowerX4SquareExpr)+
      oldHessianCoarseColumnCoefficient (originCube 2 (m+129)) 133 b (q3ModelLength (m+1))*
        inverseHistoryDiscount*Real.sqrt (mixedXiPreCap M+(1/10^12:ℝ)*theta M) := by
    have ha := old_hessian_source_multiplier_nonneg (originCube 2 (m+129)) 134 b (q3ModelLength (m+1))
    rw [old_hessian_physical_source_multiplier] at ha
    have hc : 0≤oldHessianCoarseColumnCoefficient (originCube 2 (m+129)) 133 b (q3ModelLength (m+1)) := by
      rw [old_hessian_physical_coarse_column]
      positivity
    exact add_nonneg (mul_nonneg ha (Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg hc inverse_history_discount_range.1.le) (Real.sqrt_nonneg _))
  exact (pow_le_pow_left₀ hleft hsum 2).trans_eq (by
    norm_num only [lowerDmixExpr,lowerX4Expr,lowerTExpr,evalReal,sc]
    rw [←sq_abs b]
    ring)


end
end ASDExplicitGamma.Scalar
