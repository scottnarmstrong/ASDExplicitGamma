module

public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalScales
public import ASDExplicitGamma.Native.OldSignedInitialMeanStrong

/-! The actual projected-source majorant meets the frozen S2 expression. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section

/-- The proved weak payment is below the exact frozen Xi, including its
full theta-scaled scalar-grouped reserve. -/
theorem old_hessian_weak_payment_certified (M : ABKModel 2) (hg : M.gamma≤gammaZero) :
    mixedXiPreCap M+(1/10^12:ℝ)*theta M≤evalReal scalarRealEnv lowerXiExpr := by
  have hpre : (inSourceXi5Pre:ℝ)+(1/10^12:ℝ)≤evalReal scalarRealEnv lowerXiExpr := by
    norm_num [inSourceXi5Pre,Numerics.Native.nativeSource5Result,evalReal,lowerXiExpr,sc]
  have hnon : 0≤evalReal scalarRealEnv lowerXiExpr := by norm_num [evalReal,lowerXiExpr,sc]
  calc
    _ = theta M*((inSourceXi5Pre:ℝ)+(1/10^12:ℝ)) := by unfold mixedXiPreCap; ring
    _ ≤ theta M*evalReal scalarRealEnv lowerXiExpr :=
      mul_le_mul_of_nonneg_left hpre (cold_theta_pos M).le
    _ ≤ 1*evalReal scalarRealEnv lowerXiExpr := mul_le_mul_of_nonneg_right (cold_theta_le_one M hg) hnon
    _ = _ := one_mul _

/-- The coarse column, including its root-zero discount, meets exactly
its frozen coefficient; no derivative-column factor is omitted. -/
theorem old_hessian_coarse_column_certified (m : ℤ) (b : ℝ) :
    oldHessianCoarseColumnCoefficient (originCube 2 (m+129)) 133 b (q3ModelLength (m+1))*
      inverseHistoryDiscount≤evalReal scalarRealEnv lowerColumnMixExpr*|b| := by
  have hα : inverseHistoryDiscount≤19/25 := by
    linarith only [old_signed_initial_history_tail_gates.1]
  rw [old_hessian_physical_coarse_column]
  have hh := mul_le_mul_of_nonneg_left hα
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (by norm_num : (0:ℝ)≤205069/19683000)) (abs_nonneg b))
  exact hh.trans_eq (by norm_num [evalReal,lowerColumnMixExpr,sc]; ring)

/-- The second weighted coarse trace cap is precisely the frozen L4². -/
theorem old_hessian_coarse_trace_cap_two :
    oldHessianCoarseTraceMomentCap 2=evalReal scalarRealEnv lowerL4SquareExpr := by
  norm_num [oldHessianCoarseTraceMomentCap,rareExpansionTail,Finset.sum_Icc_succ_top,
    Nat.choose,nativeSourceExactMeanCaps,evalReal,sc,lowerL4SquareExpr,lowerA4Expr,lowerHistoryExpr]

/-- The actual projected-residual envelope is integrable and paid by the
exact S2 certificate times the genuine physical shell amplitude squared. -/
theorem old_hessian_actual_source_square_certified
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    Integrable (fun ω => oldHessianGroupedBank M m ω*
      oldHessianSourceEnvelope M m b (q3ModelLength (m+1)) ω) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldHessianGroupedBank M m ω*
      oldHessianSourceEnvelope M m b (q3ModelLength (m+1)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        b^2*evalReal scalarRealEnv lowerSourceSquareExpr := by
  have hh := old_hessian_actual_source_envelope_moment M h hM hg N hpast m hm b
    (q3ModelLength (m+1)) 1 (by norm_num)
  simp only [pow_one,Nat.reduceAdd] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  rw [old_hessian_physical_source_multiplier,old_hessian_coarse_trace_cap_two]
  have hA : 0≤evalReal scalarRealEnv lowerAExpr := by
    have ha := old_hessian_source_multiplier_nonneg (originCube 2 (m+129)) 134 1 (q3ModelLength (m+1))
    rw [old_hessian_physical_source_multiplier,abs_one,mul_one] at ha
    exact ha
  have hC := old_hessian_coarse_column_certified m b
  have hweak := mul_le_mul_of_nonneg_left (old_hessian_weak_payment_certified M hg)
    (by norm_num : (0:ℝ)≤14103/10000)
  have hC0 : 0≤evalReal scalarRealEnv lowerColumnMixExpr*|b| := by
    norm_num [evalReal,lowerColumnMixExpr,sc]
  have hroot := mul_le_mul hC (Real.sqrt_le_sqrt hweak) (Real.sqrt_nonneg _) hC0
  have hsum := add_le_add (le_refl (evalReal scalarRealEnv lowerAExpr*|b| *
    Real.sqrt (evalReal scalarRealEnv lowerL4SquareExpr))) hroot
  have hleft : 0≤evalReal scalarRealEnv lowerAExpr*|b| *Real.sqrt (evalReal scalarRealEnv lowerL4SquareExpr)+
      oldHessianCoarseColumnCoefficient (originCube 2 (m+129)) 133 b (q3ModelLength (m+1))*
        inverseHistoryDiscount*Real.sqrt ((14103/10000:ℝ)*(mixedXiPreCap M+(1/10^12:ℝ)*theta M)) := by
    have ha := old_hessian_source_multiplier_nonneg (originCube 2 (m+129)) 134 b (q3ModelLength (m+1))
    rw [old_hessian_physical_source_multiplier] at ha
    have hc : 0≤oldHessianCoarseColumnCoefficient (originCube 2 (m+129)) 133 b (q3ModelLength (m+1)) := by
      rw [old_hessian_physical_coarse_column]
      positivity
    exact add_nonneg (mul_nonneg ha (Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg hc inverse_history_discount_range.1.le) (Real.sqrt_nonneg _))
  exact (pow_le_pow_left₀ hleft hsum 2).trans_eq (by
    norm_num only [lowerSourceSquareExpr,lowerL4Expr,evalReal,sc]
    rw [←sq_abs b]
    ring)

end
end ASDExplicitGamma.Scalar
