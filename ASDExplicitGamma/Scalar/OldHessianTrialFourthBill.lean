module

public import ASDExplicitGamma.Scalar.OldHessianTrialCenteredAffinePairing
public import ASDExplicitGamma.Scalar.OldHessianTrialMinusAffineReceiver

/-! The fourth OLD error bill, attached to its literal complete signed cross. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section

/-- Integrable nonnegative fourth-bill majorant in the original law. -/
def oldHessianFourthBill (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  (2*(431/500:ℝ))*(Real.sqrt (oldHessianCenteredSourceEnvelope M m b ω)*
    Real.sqrt (oldHessianMinusAffineReceiverEnvelope M m b (q3ModelLength (m+1)) ω))

/-- The literal complete centered affine cross pays exactly the fourth
frozen error expression times b². Convergence, physical spatial domination
and the correlated annealed estimate are all conclusions. -/
theorem old_hessian_actual_fourth_bill
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    Integrable (oldHessianFourthBill M m b) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        Summable (fun p => oldHessianCenteredAffineTerm M m b p ω) ∧
          |(2*(431/500:ℝ))*(∑' p,oldHessianCenteredAffineTerm M m b p ω)|≤oldHessianFourthBill M m b ω) ∧
      (∫ ω,oldHessianFourthBill M m b ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        b^2*evalReal scalarRealEnv lowerTerm4Expr := by
  have hpay := old_hessian_centered_affine_receiver_root_payment M h hM hg N hpast m hm b
  have hc : 0≤2*(431/500:ℝ) := by norm_num
  refine ⟨hpay.1.const_mul _,?_,?_⟩
  · filter_upwards [old_hessian_actual_centered_affine_pairing M h hM hg N hpast m hm b] with ω hω
    refine ⟨hω.1,?_⟩
    rw [abs_mul,abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hω.2 hc
  · change (∫ ω,(2*(431/500:ℝ))*(Real.sqrt (oldHessianCenteredSourceEnvelope M m b ω)*
      Real.sqrt (oldHessianMinusAffineReceiverEnvelope M m b (q3ModelLength (m+1)) ω))
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤_
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hpay.2 hc).trans_eq (by
      norm_num only [oldHessianCenteredSourceCap,lowerTerm4Expr,lowerHalfExpr,evalReal,sc]
      ring)

end
end ASDExplicitGamma.Scalar
