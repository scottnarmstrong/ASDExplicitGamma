module

public import ASDExplicitGamma.Scalar.OldHessianTrialCenteredEnvelope
public import ASDExplicitGamma.Scalar.OldHessianTrialDirectionalTrace
public import ASDExplicitGamma.Scalar.OldHessianTrialCoarseTracePopulation
public import ASDExplicitGamma.Native.OldSignedDirectionalProxyCongr
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedThetaTermMoment
public import ASDExplicitGamma.Scalar.OldHessianTrialDirectionalRare
public import ASDExplicitGamma.Scalar.OldHessianTrialCertifiedSource
public import ASDExplicitGamma.Scalar.OldHessianTrialTopDirectional

/-! Correlated covariance payments for the centered mixed source. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section

/-- The exact centered-source coefficient kr X4+c_mix sqrt(Xi). -/
def oldHessianCenteredSourceCap : ℝ :=
  evalReal scalarRealEnv lowerKrExpr*evalReal scalarRealEnv lowerX4Expr+
    evalReal scalarRealEnv lowerColumnMixExpr*evalReal scalarRealEnv lowerTExpr

theorem old_hessian_centered_source_cap_nonneg : 0≤oldHessianCenteredSourceCap := by
  norm_num [oldHessianCenteredSourceCap,evalReal,lowerKrExpr,lowerS1Expr,lowerS2Expr,
    lowerX4Expr,lowerTExpr,lowerColumnMixExpr,sc]
  positivity

/-- The actual centered-source majorant is integrable and meets the
precise covariance residual coefficient before contraction with its receiver. -/
theorem old_hessian_centered_source_envelope_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    Integrable (oldHessianCenteredSourceEnvelope M m b) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,oldHessianCenteredSourceEnvelope M m b ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        b^2*oldHessianCenteredSourceCap^2 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let f := fun ω => oldHessianGroupedBank M m ω*oldHessianSourceTrace M m 4 ω
  let g := oldHessianGroupedOldTheta M m
  let a := evalReal scalarRealEnv lowerKrExpr*|b|
  let c := evalReal scalarRealEnv lowerColumnMixExpr*|b|
  have htrace := old_hessian_actual_certified_trace_moments M h hM hg N hpast m hm
  have hweak := old_hessian_grouped_old_theta_moments M h hM hg N hpast m hm 0 (by norm_num)
  simp only [pow_zero,one_mul] at hweak
  have ha : 0≤a := by
    dsimp only [a]
    norm_num [evalReal,lowerKrExpr,lowerS1Expr,lowerS2Expr,sc]
    positivity
  have hc : 0≤c := by
    dsimp only [c]
    norm_num [evalReal,lowerColumnMixExpr,sc]
  have hh := old_hessian_square_expectation μ f g a c htrace.1 hweak.2.1
    (fun ω => mul_nonneg ENNReal.toReal_nonneg (old_hessian_source_trace_nonneg M m 4 ω))
    (old_hessian_grouped_old_theta_nonneg M m) ha hc
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hsum := add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htrace.2.1) ha)
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hweak.2.2.trans (old_hessian_weak_payment_certified M hg))) hc)
  exact (pow_le_pow_left₀ (add_nonneg (mul_nonneg ha (Real.sqrt_nonneg _))
    (mul_nonneg hc (Real.sqrt_nonneg _))) hsum 2).trans_eq (by
      dsimp only [a,c,oldHessianCenteredSourceCap]
      simp only [lowerX4Expr,lowerTExpr,evalReal]
      rw [←sq_abs b]
      ring)

end
end ASDExplicitGamma.Scalar
