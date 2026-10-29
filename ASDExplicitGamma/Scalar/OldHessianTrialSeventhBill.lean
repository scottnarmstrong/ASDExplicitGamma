module

public import ASDExplicitGamma.Scalar.OldHessianTrialSourceOscillationPairing
public import ASDExplicitGamma.Scalar.OldHessianTrialUnweightedSourceSquare
public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalOscillation

/-! Exact seventh OLD bill on the literal full source/reciprocal oscillation cross. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Correlated integrable majorant of the actual seventh cross. -/
def oldHessianSeventhBill (M : ABKModel 2) (m : ℤ) (b : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (2*(431/500:ℝ))*(Real.sqrt (oldHessianSourceEnvelope M m b (q3ModelLength (m+1)) ω)*
    Real.sqrt (oldHessianGroupedBank M m ω*
      oldHessianFlatMatrixEnergy M m b (q3ModelLength (m+1)) ω))

/-- The full correlated source/oscillation envelope pays precisely
2 lambda d sqrt(beta Mstar) o, retaining the original cell and mode labels. -/
theorem old_hessian_actual_seventh_bill
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    Integrable (oldHessianSeventhBill M m b) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun p => oldHessianSourceOscillationTerm M m b p ω) ∧
      |(2*(431/500:ℝ))*(∑' p,oldHessianSourceOscillationTerm M m b p ω)|≤oldHessianSeventhBill M m b ω) ∧
    (∫ ω,oldHessianSeventhBill M m b ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      b^2*evalReal scalarRealEnv lowerTerm7Expr := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let f := oldHessianSourceEnvelope M m b (q3ModelLength (m+1))
  let g := fun ω => oldHessianGroupedBank M m ω*
    oldHessianFlatMatrixEnergy M m b (q3ModelLength (m+1)) ω
  have hs := old_hessian_actual_unweighted_source_square M h hM hg N hpast m hm b
  have hr := old_hessian_physical_banked_matrix_moment M h hM hg N hpast m hm b
  have hg0 (ω) : 0≤g ω := by
    apply mul_nonneg ENNReal.toReal_nonneg
    apply old_signed_cell_average_nonneg
    intro U
    apply mul_nonneg _ (sq_nonneg _)
    exact add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num)
      (old_hessian_cell_max_trace_nonneg M m U.val U.property ω))) (Real.sqrt_nonneg _)
  have hh := old_signed_sqrt_product_expectation μ f g hs.1 hr.1 (fun _ => sq_nonneg _) hg0
  have hp := old_hessian_actual_source_oscillation_pairing M h hM hg N hpast m hm b
  refine ⟨hh.1.const_mul _,?_,?_⟩
  · filter_upwards [hp] with ω hω
    refine ⟨hω.1,?_⟩
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2*(431/500))]
    exact mul_le_mul_of_nonneg_left hω.2 (by norm_num)
  · change (∫ ω,(2*(431/500:ℝ))*(Real.sqrt (f ω)*Real.sqrt (g ω)) ∂μ)≤_
    rw [integral_const_mul]
    have hcap := hh.2.trans (mul_le_mul (Real.sqrt_le_sqrt hs.2) (Real.sqrt_le_sqrt hr.2)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hd : 0≤evalReal scalarRealEnv lowerDmixExpr := by
      change 0≤evalReal scalarRealEnv lowerAExpr*Real.sqrt (evalReal scalarRealEnv lowerX4SquareExpr)+
        evalReal scalarRealEnv lowerColumnMixExpr*Real.sqrt (evalReal scalarRealEnv lowerXiExpr)
      have ha := old_hessian_source_multiplier_nonneg (originCube 2 (m+129)) 134 1 (q3ModelLength (m+1))
      rw [old_hessian_physical_source_multiplier,abs_one,mul_one] at ha
      exact add_nonneg (mul_nonneg ha (Real.sqrt_nonneg _))
        (mul_nonneg (by norm_num [evalReal,lowerColumnMixExpr,sc]) (Real.sqrt_nonneg _))
    have ho : 0≤evalReal scalarRealEnv lowerOscillationExpr := by
      norm_num [evalReal,lowerOscillationExpr,lowerS1Expr,sc]
    have hmat : 0≤(14103/10000:ℝ)*evalReal scalarRealEnv lowerMExpr := by
      norm_num [evalReal,lowerMExpr,sc]
      positivity
    rw [Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq_eq_abs,Real.sqrt_sq hd,
      Real.sqrt_mul hmat,Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq_eq_abs,Real.sqrt_sq ho] at hcap
    apply (mul_le_mul_of_nonneg_left hcap (by norm_num : (0:ℝ)≤2*(431/500))).trans_eq
    norm_num only [lowerTerm7Expr,lowerSmExpr,lowerDmixExpr,evalReal,sc]
    rw [←sq_abs b]
    ring

end
end ASDExplicitGamma.Scalar
