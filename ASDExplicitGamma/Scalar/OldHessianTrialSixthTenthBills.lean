module

public import ASDExplicitGamma.Scalar.OldHessianTrialMinusFeedbackProfile
public import ASDExplicitGamma.Scalar.OldHessianTrialMinusFeedbackMoments

/-! Exact sixth and tenth bills for the original complete minus correction. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section

/-- Both original correction payments are attached to the literal complete
white-mode feedback, with no projection or estimate premise. -/
theorem old_hessian_actual_sixth_tenth_bills
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    Integrable (oldHessianSixthBill M m b) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    Integrable (oldHessianTenthBill M m b) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun n => oldHessianMinusFeedbackTerm M m b n ω) ∧
      |∑' n,oldHessianMinusFeedbackTerm M m b n ω|≤
        oldHessianSixthBill M m b ω+oldHessianTenthBill M m b ω) ∧
    (∫ ω,oldHessianSixthBill M m b ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤b^2*evalReal scalarRealEnv lowerTerm6Expr ∧
    (∫ ω,oldHessianTenthBill M m b ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤b^2*evalReal scalarRealEnv lowerTerm10Expr := by
  have hi := old_hessian_minus_feedback_moments M h hM hg N hpast m hm b
  refine ⟨hi.1.1,hi.2.1,?_,hi.1.2,hi.2.2⟩
  filter_upwards [old_hessian_actual_minus_feedback_profile M h hM hg N hpast m hm b,
    old_hessian_actual_parent_bottom_pair_le_theta M h hM hg N hpast m hm] with ω hω hp
  refine ⟨hω.1,hω.2.trans ?_⟩
  have hc : 0≤2*(431/500:ℝ)*(evalReal scalarRealEnv lowerKappaExpr*|b|) := by
    apply mul_nonneg (by norm_num)
    exact mul_nonneg (by norm_num [evalReal,lowerKappaExpr,sc]) (abs_nonneg b)
  have ho : 0≤evalReal scalarRealEnv lowerOscillationExpr := by
    norm_num [evalReal,lowerOscillationExpr,lowerS1Expr,sc]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl (Real.sqrt 2)) (Real.sqrt_le_sqrt hp)) hc)
    (add_nonneg (add_nonneg
      (Real.sqrt_nonneg (oldHessianMinusAffineReceiverEnvelope M m b (q3ModelLength (m+1)) ω))
      (Real.sqrt_nonneg (oldHessianGroupedBank M m ω*oldHessianFlatMatrixEnergy M m b (q3ModelLength (m+1)) ω)))
      (mul_nonneg (abs_nonneg b) ho))
  exact hh.trans_eq (by dsimp only [oldHessianSixthBill,oldHessianTenthBill]; ring)

end
end ASDExplicitGamma.Scalar
