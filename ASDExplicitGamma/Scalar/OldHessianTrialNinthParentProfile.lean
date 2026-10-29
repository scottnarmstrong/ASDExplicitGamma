module

public import ASDExplicitGamma.Scalar.OldHessianTrialMixedFeedbackMoments
public import ASDExplicitGamma.Scalar.OldHessianTrialParentBottomPair

/-! Exact ninth-bill moment for the actual parent profile in mixed feedback. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section

/-- Two correlated square-root bank factors restore precisely one bank. -/
theorem old_hessian_bank_root_product (B f g : ℝ) (hB : 0≤B) :
    Real.sqrt (B*f)*Real.sqrt (B*g)=B*Real.sqrt f*Real.sqrt g := by
  rw [Real.sqrt_mul hB,Real.sqrt_mul hB]
  calc
    _ = (Real.sqrt B)^2*(Real.sqrt f*Real.sqrt g) := by ring
    _ = _ := by rw [Real.sq_sqrt hB]; ring

/-- Correlated ninth-bill envelope with the unchanged full source and
actual OLD grouped weak proxy. -/
def oldHessianNinthBill (M : ABKModel 2) (m : ℤ) (b : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let B := oldHessianGroupedBank M m ω
  let S := oldHessianSourceEnvelope M m b (q3ModelLength (m+1)) ω
  let Θ := oldHessianGroupedOldTheta M m ω
  (2*evalReal scalarRealEnv lowerKappaExpr*|b| *(63/50:ℝ))*
    (Real.sqrt 2*(B*Real.sqrt S)+Real.sqrt (B*S)*Real.sqrt (B*Θ))

/-- The intrinsic actual parent profile in the mixed feedback is dominated
by this integrable ninth-bill envelope, with its exact certified moment.
The separate spatial derivative pairing remains to be identified by its consumer. -/
theorem old_hessian_ninth_parent_profile_bill
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    Integrable (oldHessianNinthBill M m b) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      (2*evalReal scalarRealEnv lowerKappaExpr*|b| *(63/50:ℝ))*
        (Real.sqrt 2*(oldHessianGroupedBank M m ω*
          Real.sqrt (oldHessianSourceEnvelope M m b (q3ModelLength (m+1)) ω))+
        oldHessianGroupedBank M m ω*Real.sqrt (oldHessianSourceEnvelope M m b (q3ModelLength (m+1)) ω)*
          Real.sqrt (oldHessianParentBottomPairEnergy M m ω))≤oldHessianNinthBill M m b ω) ∧
    (∫ ω,oldHessianNinthBill M m b ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      b^2*evalReal scalarRealEnv lowerTerm9Expr := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let B := oldHessianGroupedBank M m
  let S := oldHessianSourceEnvelope M m b (q3ModelLength (m+1))
  let Θ := oldHessianGroupedOldTheta M m
  let c := 2*evalReal scalarRealEnv lowerKappaExpr*|b| *(63/50:ℝ)
  have hc : 0≤c := by
    apply mul_nonneg _ (by norm_num)
    exact mul_nonneg (by norm_num [evalReal,lowerKappaExpr,sc]) (abs_nonneg b)
  have hfirst := old_hessian_banked_source_root_moment M h hM hg N hpast m hm b
  have hsecond := old_hessian_source_parent_root_moment M h hM hg N hpast m hm b
  have hi := (hfirst.1.const_mul (Real.sqrt 2)).add hsecond.1
  refine ⟨hi.const_mul c,?_,?_⟩
  · filter_upwards [old_hessian_actual_parent_bottom_pair_le_theta M h hM hg N hpast m hm] with ω hω
    change c*(Real.sqrt 2*(B ω*Real.sqrt (S ω))+B ω*Real.sqrt (S ω)*
      Real.sqrt (oldHessianParentBottomPairEnergy M m ω))≤
        c*(Real.sqrt 2*(B ω*Real.sqrt (S ω))+Real.sqrt (B ω*S ω)*Real.sqrt (B ω*Θ ω))
    have hB : 0≤B ω := ENNReal.toReal_nonneg
    rw [old_hessian_bank_root_product (B ω) (S ω) (Θ ω) hB]
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hω) (mul_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg _)))) hc
  · change (∫ ω,c*(Real.sqrt 2*(B ω*Real.sqrt (S ω))+Real.sqrt (B ω*S ω)*Real.sqrt (B ω*Θ ω)) ∂μ)≤_
    rw [integral_const_mul,integral_add (hfirst.1.const_mul (Real.sqrt 2)) hsecond.1,integral_const_mul]
    have hh := mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left hfirst.2 (Real.sqrt_nonneg 2)) hsecond.2) hc
    exact hh.trans_eq (by
      dsimp only [c]
      norm_num only [lowerTerm9Expr,lowerKappaExpr,evalReal,sc]
      rw [←sq_abs b]
      ring)

end
end ASDExplicitGamma.Scalar
