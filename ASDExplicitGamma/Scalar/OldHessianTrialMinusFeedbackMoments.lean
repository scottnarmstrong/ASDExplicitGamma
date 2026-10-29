module

public import ASDExplicitGamma.Scalar.OldHessianTrialOffsetRootMoment
public import ASDExplicitGamma.Scalar.OldHessianTrialMinusAffineReceiver
public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalOscillation

/-! Exact sixth and tenth OLD payments, preserving the correlated bank. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The original affine part of the minus correction feedback. -/
def oldHessianSixthBill (M : ABKModel 2) (m : ℤ) (b : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (2*(431/500:ℝ)*evalReal scalarRealEnv lowerKappaExpr*|b|)*
    ((Real.sqrt 2+Real.sqrt (oldHessianGroupedOldTheta M m ω))*
      Real.sqrt (oldHessianMinusAffineReceiverEnvelope M m b (q3ModelLength (m+1)) ω))

/-- The bank-weighted matrix oscillation and the reciprocal offset. -/
def oldHessianTenthBill (M : ABKModel 2) (m : ℤ) (b : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (2*(431/500:ℝ)*evalReal scalarRealEnv lowerKappaExpr*|b|)*
    ((Real.sqrt 2+Real.sqrt (oldHessianGroupedOldTheta M m ω))*
      (Real.sqrt (oldHessianGroupedBank M m ω*oldHessianFlatMatrixEnergy M m b (q3ModelLength (m+1)) ω)+
        |b| *evalReal scalarRealEnv lowerOscillationExpr))

/-- Both correction payments have their exact certified first moments.
The random bank is kept inside the matrix energy until after contraction. -/
theorem old_hessian_minus_feedback_moments
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    (Integrable (oldHessianSixthBill M m b) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,oldHessianSixthBill M m b ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
        b^2*evalReal scalarRealEnv lowerTerm6Expr) ∧
    (Integrable (oldHessianTenthBill M m b) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,oldHessianTenthBill M m b ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
        b^2*evalReal scalarRealEnv lowerTerm10Expr) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Θ := oldHessianGroupedOldTheta M m
  let A := oldHessianMinusAffineReceiverEnvelope M m b (q3ModelLength (m+1))
  let F := fun ω => oldHessianGroupedBank M m ω*oldHessianFlatMatrixEnergy M m b (q3ModelLength (m+1)) ω
  let X := evalReal scalarRealEnv lowerXiExpr
  let D := (14103/10000:ℝ)*evalReal scalarRealEnv lowerMExpr
  let o := evalReal scalarRealEnv lowerOscillationExpr
  let c := 2*(431/500:ℝ)*evalReal scalarRealEnv lowerKappaExpr*|b|
  have hc : 0≤c := mul_nonneg (by norm_num [evalReal,lowerKappaExpr,sc]) (abs_nonneg b)
  have hX : 0≤X := by norm_num [X,evalReal,lowerXiExpr,sc]
  have hD : 0≤D := by norm_num [D,evalReal,lowerMExpr,sc]; positivity
  have ho : 0≤o := by norm_num [o,evalReal,lowerOscillationExpr,lowerS1Expr,sc]
  have hθ0 := old_hessian_grouped_old_theta_nonneg M m
  have hθ := old_hessian_grouped_old_theta_moments M h hM hg N hpast m hm 0 (by norm_num)
  simp only [pow_zero,one_mul] at hθ
  have hθcap : (∫ ω,Θ ω ∂μ)≤X := hθ.2.2.trans (old_hessian_weak_payment_certified M hg)
  have hA := old_hessian_actual_minus_affine_receiver_moment M h hM hg N hpast m hm b (q3ModelLength (m+1))
  have hF := old_hessian_physical_banked_matrix_moment M h hM hg N hpast m hm b
  have hnF ω : 0≤F ω := by
    apply mul_nonneg ENNReal.toReal_nonneg
    apply old_signed_cell_average_nonneg
    intro U
    apply mul_nonneg _ (sq_nonneg _)
    exact add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num)
      (old_hessian_cell_max_trace_nonneg M m U.val U.property ω))) (Real.sqrt_nonneg _)
  have h6 := old_hessian_offset_root_product_expectation μ Θ A (Real.sqrt 2) 0 hθ.2.1 hA.1
    hθ0 (old_hessian_minus_affine_receiver_envelope_nonneg M m b _) (Real.sqrt_nonneg _) le_rfl
  simp only [add_zero] at h6
  have h10 := old_hessian_offset_root_product_expectation μ Θ F (Real.sqrt 2) (|b| *o) hθ.2.1 hF.1
    hθ0 hnF (Real.sqrt_nonneg _) (mul_nonneg (abs_nonneg b) ho)
  have hrA : Real.sqrt (∫ ω,A ω ∂μ)≤|b| *Real.sqrt (X/2) := by
    have hh := Real.sqrt_le_sqrt hA.2
    rw [mul_div_assoc,Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq_eq_abs] at hh
    exact hh
  have hrF : Real.sqrt (∫ ω,F ω ∂μ)≤Real.sqrt D*(|b| *o) := by
    have hh := Real.sqrt_le_sqrt hF.2
    rw [Real.sqrt_mul hD,Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq_eq_abs,Real.sqrt_sq ho] at hh
    exact hh
  have h6cap := h6.2.trans (mul_le_mul (add_le_add (le_refl (Real.sqrt 2)) (Real.sqrt_le_sqrt hθcap)) hrA
    (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  have h10cap := h10.2.trans (mul_le_mul (add_le_add (le_refl (Real.sqrt 2)) (Real.sqrt_le_sqrt hθcap))
    (add_le_add hrF (le_refl (|b| *o)))
    (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (abs_nonneg b) ho))
    (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  refine ⟨⟨h6.1.const_mul c,?_⟩,⟨h10.1.const_mul c,?_⟩⟩
  · change (∫ ω,c*((Real.sqrt 2+Real.sqrt (Θ ω))*Real.sqrt (A ω)) ∂μ)≤_
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left h6cap hc).trans_eq (by
      dsimp only [c,X]
      norm_num only [lowerTerm6Expr,lowerTExpr,lowerHalfExpr,lowerKappaExpr,evalReal,sc]
      rw [←sq_abs b]; ring)
  · change (∫ ω,c*((Real.sqrt 2+Real.sqrt (Θ ω))*(Real.sqrt (F ω)+|b| *o)) ∂μ)≤_
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left h10cap hc).trans_eq (by
      dsimp only [c,X,D,o]
      norm_num only [lowerTerm10Expr,lowerTExpr,lowerSmExpr,lowerKappaExpr,evalReal,sc]
      rw [←sq_abs b]; ring)

end
end ASDExplicitGamma.Scalar
