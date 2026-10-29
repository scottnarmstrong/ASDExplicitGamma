module

public import ASDExplicitGamma.Scalar.OldHessianTrialMinusMeanBank
public import ASDExplicitGamma.Scalar.OldHessianTrialCenteredMoment

/-! Complete original minus affine receiver and its correlated source pairing. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Every original finite-parent minus mean column is fed into the actual
uniform fine-cell directional proxy, before the full mode sum. -/
def oldHessianMinusAffineReceiverEnvelope (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑' p : whiteBasisIndex×Fin 2,oldSignedCellAverage (originCube 2 (m+129)) 134
    (fun U => oldHessianCellDirectionalTheta M m U.val
      (oldHessianMinusMeanColumn (originCube 2 (m+129)) 134 b L p U) ω)

theorem old_hessian_minus_affine_receiver_envelope_nonneg (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) :
    0≤oldHessianMinusAffineReceiverEnvelope M m b L ω :=
  tsum_nonneg (fun _p => old_signed_cell_average_nonneg _ _ _ (fun U =>
    old_hessian_cell_directional_theta_nonneg M m U.val U.property _ ω))

/-- The complete original affine minus receiver is integrable and pays
b² Xi/2, with its actual mean-square bank proved internally. -/
theorem old_hessian_actual_minus_affine_receiver_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    Integrable (oldHessianMinusAffineReceiverEnvelope M m b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,oldHessianMinusAffineReceiverEnvelope M m b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        b^2*evalReal scalarRealEnv lowerXiExpr/2 := by
  have hbank := old_hessian_minus_mean_bank (originCube 2 (m+129)) 134 b L
  have hs := old_hessian_cell_directional_weighted_series M h hM hg N hpast m hm
    (oldHessianMinusMeanColumn (originCube 2 (m+129)) 134 b L) hbank.1
  have hC : 0≤evalReal scalarRealEnv lowerXiExpr/2 := by norm_num [evalReal,lowerXiExpr,sc]
  refine ⟨hs.2.1,hs.2.2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left hbank.2 hC).trans_eq (by ring)

/-- The centered mixed source and the complete original affine minus
receiver are contracted in their common law, yielding the exact fourth bill. -/
theorem old_hessian_centered_affine_receiver_root_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    Integrable (fun ω => Real.sqrt (oldHessianCenteredSourceEnvelope M m b ω)*
      Real.sqrt (oldHessianMinusAffineReceiverEnvelope M m b (q3ModelLength (m+1)) ω))
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,Real.sqrt (oldHessianCenteredSourceEnvelope M m b ω)*
        Real.sqrt (oldHessianMinusAffineReceiverEnvelope M m b (q3ModelLength (m+1)) ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          b^2*oldHessianCenteredSourceCap*Real.sqrt (evalReal scalarRealEnv lowerXiExpr/2) := by
  have hs := old_hessian_centered_source_envelope_moment M h hM hg N hpast m hm b
  have hr := old_hessian_actual_minus_affine_receiver_moment M h hM hg N hpast m hm b (q3ModelLength (m+1))
  have hh := old_signed_sqrt_product_expectation (Cutoff.cutoffSampleLaw M).toMeasure _ _ hs.1 hr.1
    (fun _ => sq_nonneg _) (old_hessian_minus_affine_receiver_envelope_nonneg M m b _)
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hcap := mul_le_mul (Real.sqrt_le_sqrt hs.2) (Real.sqrt_le_sqrt hr.2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have he1 : Real.sqrt (b^2*oldHessianCenteredSourceCap^2)=|b| *oldHessianCenteredSourceCap := by
    rw [Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq_eq_abs,Real.sqrt_sq old_hessian_centered_source_cap_nonneg]
  have he2 : Real.sqrt (b^2*evalReal scalarRealEnv lowerXiExpr/2)=|b| *Real.sqrt (evalReal scalarRealEnv lowerXiExpr/2) := by
    rw [mul_div_assoc,Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq_eq_abs]
  rw [he1,he2] at hcap
  exact hcap.trans_eq (by rw [←sq_abs b]; ring)

end
end ASDExplicitGamma.Scalar
