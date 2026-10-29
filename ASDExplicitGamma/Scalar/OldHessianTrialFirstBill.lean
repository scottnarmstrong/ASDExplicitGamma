module

public import ASDExplicitGamma.Scalar.OldHessianTrialMinusFlatEnvelope
public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalOscillation

/-! Exact first OLD bill, keeping the unchanged fine affine penalty separate. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The exact matrix oscillation moment at the physical fine mesh. -/
theorem old_hessian_physical_matrix_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    Integrable (oldHessianFlatMatrixEnergy M m b (q3ModelLength (m+1))) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldHessianFlatMatrixEnergy M m b (q3ModelLength (m+1)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      evalReal scalarRealEnv lowerMExpr*(b^2*(evalReal scalarRealEnv lowerOscillationExpr)^2) := by
  have hh := old_hessian_flat_matrix_moment M h hM hg N hpast m hm b (q3ModelLength (m+1))
  refine ⟨hh.1,hh.2.trans (mul_le_mul_of_nonneg_left (old_hessian_physical_minus_oscillation m b) ?_)⟩
  norm_num [evalReal,lowerMExpr,sc]
  positivity

/-- First-bill majorant: only the oscillation cross and oscillation square;
the exact original affine energy is retained separately. -/
def oldHessianFirstBill (M : ABKModel 2) (m : ℤ) (b : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let L := q3ModelLength (m+1)
  (431/500:ℝ)^2*(2*(Real.sqrt (oldHessianMinusAffineEnergy M m b L ω)*
    Real.sqrt (oldHessianFlatMatrixEnergy M m b L ω))+oldHessianFlatMatrixEnergy M m b L ω)

/-- The actual unchanged fine Z energy pays its separate affine term and
precisely lambda squared Unew; no affine or oscillation cap is assumed. -/
theorem old_hessian_actual_first_bill
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    Integrable (oldHessianFirstBill M m b) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∀ ω,(431/500:ℝ)^2*(∑' n,oldHessianMinusFlatEnergyTerm M m b (q3ModelLength (m+1)) n ω)≤
      (431/500:ℝ)^2*oldHessianMinusAffineEnergy M m b (q3ModelLength (m+1)) ω+oldHessianFirstBill M m b ω) ∧
    (∫ ω,oldHessianFirstBill M m b ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      b^2*evalReal scalarRealEnv lowerTerm1Expr := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let L := q3ModelLength (m+1)
  let A := oldHessianMinusAffineEnergy M m b L
  let F := oldHessianFlatMatrixEnergy M m b L
  let C := 1+evalReal scalarRealEnv lowerA5Expr/2
  let D := evalReal scalarRealEnv lowerMExpr
  let o := evalReal scalarRealEnv lowerOscillationExpr
  have hA := old_hessian_minus_affine_energy_moment M h hM hg N hpast m hm b L
  have hF := old_hessian_physical_matrix_moment M h hM hg N hpast m hm b
  have hnA (ω) : 0≤A ω := tsum_nonneg (fun p => old_hessian_minus_affine_energy_term_nonneg M m b L p ω)
  have hnF (ω) : 0≤F ω := by
    apply old_signed_cell_average_nonneg
    intro U
    apply mul_nonneg _ (sq_nonneg _)
    exact add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num)
      (old_hessian_cell_max_trace_nonneg M m U.val U.property ω))) (Real.sqrt_nonneg _)
  have hr := old_signed_sqrt_product_expectation μ A F hA.2.1 hF.1 hnA hnF
  have hi := (hr.1.const_mul 2).add hF.1
  refine ⟨hi.const_mul _,?_,?_⟩
  · intro ω
    have hh := mul_le_mul_of_nonneg_left (old_hessian_actual_minus_flat_envelope M m b L ω).2
      (sq_nonneg (431/500:ℝ))
    exact hh.trans_eq (by dsimp only [oldHessianFirstBill,L]; ring)
  · change (∫ ω,(431/500:ℝ)^2*(2*(Real.sqrt (A ω)*Real.sqrt (F ω))+F ω) ∂μ)≤_
    rw [integral_const_mul,integral_add (hr.1.const_mul 2) hF.1,integral_const_mul]
    have hcap := hr.2.trans (mul_le_mul (Real.sqrt_le_sqrt hA.2.2) (Real.sqrt_le_sqrt hF.2)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have hC : 0≤C := by norm_num [C,evalReal,lowerA5Expr,sc]
    have hD : 0≤D := by norm_num [D,evalReal,lowerMExpr,sc]; positivity
    have ho : 0≤o := by norm_num [o,evalReal,lowerOscillationExpr,lowerS1Expr,sc]
    have he : Real.sqrt (C*b^2)*Real.sqrt (D*(b^2*o^2))=b^2*Real.sqrt (C*D)*o := by
      rw [Real.sqrt_mul hC,Real.sqrt_sq_eq_abs,Real.sqrt_mul hD,
        Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq_eq_abs,Real.sqrt_sq ho]
      calc
        _ = b^2*(Real.sqrt C*Real.sqrt D)*o := by rw [←sq_abs b]; ring
        _ = _ := by rw [←Real.sqrt_mul hC]
    change _≤Real.sqrt (C*b^2)*Real.sqrt (D*(b^2*o^2)) at hcap
    rw [he] at hcap
    have hh := mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left hcap (by norm_num : (0:ℝ)≤2)) hF.2) (sq_nonneg (431/500:ℝ))
    exact hh.trans_eq (by
      dsimp only [C,D,o]
      norm_num only [lowerTerm1Expr,lowerUnewExpr,evalReal,sc]
      ring)

end
end ASDExplicitGamma.Scalar
