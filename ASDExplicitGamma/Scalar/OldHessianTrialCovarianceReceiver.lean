module

public import ASDExplicitGamma.Scalar.OldHessianTrialCellDirectionalWeights
public import ASDExplicitGamma.Scalar.OldHessianTrialFrozenErrorFrobenius
public import ASDExplicitGamma.Scalar.OldHessianTrialMeanCovariancePairing
public import ASDExplicitGamma.Scalar.OldHessianTrialCertifiedTraceMoments

/-! The deterministic cell-varying covariance error receives its own
uniform directional half bound before the joint probability contraction. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The complete two-column deterministic Eminus receiver proxy. -/
def oldHessianCovarianceReceiverEnvelope (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑ i : Fin 2,oldSignedCellAverage (originCube 2 (m+129)) 134 (fun U =>
    oldHessianCellDirectionalTheta M m U.val
      (matVecMul (oldHessianMeanCovarianceError (originCube 2 (m+129)) U.val b L) (basisVec i)) ω)

/-- Its deterministic column budget is exactly the actual weighted
Frobenius covariance-error energy, with no coordinate-count loss. -/
theorem old_hessian_covariance_receiver_column_budget (Q : TriadicCube 2) (fine : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    (∑ i : Fin 2,oldSignedCellAverage Q fine (fun U =>
      vecNormSq (matVecMul (oldHessianMeanCovarianceError Q U.val b L) (basisVec i))))=
      oldSignedCellAverage Q fine (fun U => oldHessianCovarianceErrorCellEnergy Q U.val b L) := by
  rw [←old_signed_cell_average_sum]
  apply congrArg (oldSignedCellAverage Q fine)
  funext U
  simp only [old_hessian_matrix_basis_column,vecNormSq,vecDot,oldHessianCovarianceErrorCellEnergy,pow_two]

theorem old_hessian_covariance_receiver_envelope_nonneg (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) :
    0≤oldHessianCovarianceReceiverEnvelope M m b L ω :=
  Finset.sum_nonneg (fun _i _ => old_signed_cell_average_nonneg _ _ _ (fun U =>
    old_hessian_cell_directional_theta_nonneg M m U.val U.property _ ω))

/-- The actual deterministic Eminus columns receive Xi/2 times their
own Frobenius energy, after their cell dependence has been retained. -/
theorem old_hessian_covariance_receiver_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    Integrable (oldHessianCovarianceReceiverEnvelope M m b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,oldHessianCovarianceReceiverEnvelope M m b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (evalReal scalarRealEnv lowerXiExpr/2)*oldSignedCellAverage (originCube 2 (m+129)) 134
          (fun U => oldHessianCovarianceErrorCellEnergy (originCube 2 (m+129)) U.val b L) := by
  have hs := old_hessian_cell_directional_weighted_series M h hM hg N hpast m hm
    (fun (i : Fin 2) U => matVecMul
      (oldHessianMeanCovarianceError (originCube 2 (m+129)) U.val b L) (basisVec i)) Summable.of_finite
  simp only [tsum_fintype] at hs
  refine ⟨hs.2.1,hs.2.2.trans_eq ?_⟩
  rw [old_hessian_covariance_receiver_column_budget]

/-- Correlated source/covariance-error receiver contraction, preserving
both the X4 source payment and the actual deterministic Frobenius norm. -/
theorem old_hessian_covariance_receiver_root_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    Integrable (fun ω => Real.sqrt (oldHessianGroupedBank M m ω*oldHessianSourceTrace M m 4 ω)*
      Real.sqrt (oldHessianCovarianceReceiverEnvelope M m b L ω)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,Real.sqrt (oldHessianGroupedBank M m ω*oldHessianSourceTrace M m 4 ω)*
        Real.sqrt (oldHessianCovarianceReceiverEnvelope M m b L ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          evalReal scalarRealEnv lowerX4Expr*Real.sqrt (evalReal scalarRealEnv lowerXiExpr/2)*
            Real.sqrt (oldSignedCellAverage (originCube 2 (m+129)) 134
              (fun U => oldHessianCovarianceErrorCellEnergy (originCube 2 (m+129)) U.val b L)) := by
  have ht := old_hessian_actual_certified_trace_moments M h hM hg N hpast m hm
  have hr := old_hessian_covariance_receiver_moment M h hM hg N hpast m hm b L
  have hh := old_signed_sqrt_product_expectation (Cutoff.cutoffSampleLaw M).toMeasure _ _ ht.1 hr.1
    (fun ω => mul_nonneg ENNReal.toReal_nonneg (old_hessian_source_trace_nonneg M m 4 ω))
    (old_hessian_covariance_receiver_envelope_nonneg M m b L)
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hc := mul_le_mul (Real.sqrt_le_sqrt ht.2.1) (Real.sqrt_le_sqrt hr.2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hXi : 0≤evalReal scalarRealEnv lowerXiExpr/2 := by norm_num [evalReal,lowerXiExpr,sc]
  rw [Real.sqrt_mul hXi] at hc
  exact hc.trans_eq (by simp only [lowerX4Expr,evalReal]; ring)

end
end ASDExplicitGamma.Scalar
