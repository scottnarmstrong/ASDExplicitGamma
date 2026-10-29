module

public import ASDExplicitGamma.Scalar.OldHessianTrialMinusFeedbackPairedGlobal
public import ASDExplicitGamma.Scalar.OldHessianTrialMinusFeedbackSpatial
public import ASDExplicitGamma.Scalar.OldHessianTrialMinusDirectionalProxy
public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalDerivativeKappa
public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalOscillation
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedHistoryAdapter
public import ASDExplicitGamma.Scalar.OldHessianTrialMatrixHistoryControl

/-! Actual original minus feedback, with no substituted source or projection. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The actual minus correction feedback; the global flat tangent remains
separate for its exact covariance cancellation. -/
def oldHessianMinusFeedbackTerm (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (n : whiteBasisIndex) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let σ := Annealed.sigmaBar M m
  let C := oldSignedPointwiseShear (q3Convolution b (q3ModelLength (m+1)) h3Zero (whiteBasis n))
  let S := fun i => oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 k (blockBasis (Sum.inr i))
  2*(431/500:ℝ)*((∑ i : Fin 2,oldSignedEnergyPairing Q M.nu σ k (S i)
    (C (oldSignedPatchedMinus Q 134 M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k b (q3ModelLength (m+1)) n i)))-
    ∑ i : Fin 2,oldSignedEnergyPairing Q M.nu σ k (S i)
      (C (oldSignedFlatMinusBlock Q b (q3ModelLength (m+1)) n i)))

/-- The literal complete correction cross is paid by the original mean
proxy, the same banked matrix oscillation, and the paired parent profile. -/
theorem old_hessian_actual_minus_feedback_profile
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun n => oldHessianMinusFeedbackTerm M m b n ω) ∧
      |∑' n,oldHessianMinusFeedbackTerm M m b n ω|≤
        (2*(431/500:ℝ)*(evalReal scalarRealEnv lowerKappaExpr*|b|))*
        (Real.sqrt 2+Real.sqrt (oldHessianParentBottomPairEnergy M m ω))*
        (Real.sqrt (oldHessianMinusAffineReceiverEnvelope M m b (q3ModelLength (m+1)) ω)+
          Real.sqrt (oldHessianGroupedBank M m ω*oldHessianFlatMatrixEnergy M m b (q3ModelLength (m+1)) ω)+
          |b| *evalReal scalarRealEnv lowerOscillationExpr) := by
  filter_upwards [old_hessian_actual_fine_histories_le_bank M h hM hg N hpast m hm,
    old_hessian_actual_minus_directional_proxy M h hM hg N hpast m hm b (q3ModelLength (m+1))] with ω hbank hproxy
  let Q := originCube 2 (m+129)
  let L := q3ModelLength (m+1)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let σ := Annealed.sigmaBar M m
  let a := responseFramePlanarCoefficientField M.nu σ k
  let κ := evalReal scalarRealEnv lowerKappaExpr*|b|
  let β := oldHessianGroupedBank M m ω
  let K := fun U : OldSignedCellIndex Q 134 => oldSignedDerivativeKappa (cubeScaleFactor U.val) b L.val
  let G := fun U : OldSignedCellIndex Q 134 => oldHessianBottomPairedCellEnergy Q U.val M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 k
  let P := fun U : OldSignedCellIndex Q 134 => oldSignedFlatDirectionalMeanProxy Q U.val a b L false
  let H := fun U : OldSignedCellIndex Q 134 => oldSignedInverseHistory U.val a*oldSignedResponseHistory U.val a
  let O := fun U : OldSignedCellIndex Q 134 => oldSignedFlatOscillationSize Q U.val b L false
  have hκ : 0≤κ := mul_nonneg (by norm_num [evalReal,lowerKappaExpr,sc]) (abs_nonneg b)
  have ho : 0≤evalReal scalarRealEnv lowerOscillationExpr := by
    norm_num [evalReal,lowerOscillationExpr,lowerS1Expr,sc]
  have hH U : 0≤H U := by
    apply mul_nonneg
    · exact lemmaVInverseHistory_nonneg U.val a (Real.one_lt_rpow (by norm_num) (by norm_num))
    · exact ENNReal.toReal_nonneg
  have hHO : oldSignedCellAverage Q 134 (fun U => H U*O U^2)≤
      β*oldHessianFlatMatrixEnergy M m b L ω := by
    rw [oldHessianFlatMatrixEnergy,←old_signed_cell_average_mul]
    apply old_signed_cell_average_mono
    intro U
    change H U*O U^2≤β*(oldHessianCellMatrixMajorant M m U.val ω*O U^2)
    rw [←mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hB := (old_hessian_fine_history_le Q 134 M.nu σ k U.val U.property).trans (hbank 5 (by norm_num))
    exact mul_le_mul hB (old_hessian_cell_matrix_history_bounds M m U.val ω).1
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hOcap : oldSignedCellAverage Q 134 (fun U => O U^2)≤(|b| *evalReal scalarRealEnv lowerOscillationExpr)^2 := by
    rw [old_signed_cell_average_eq_descendantsAverage Q 134 (fun U => oldSignedFlatOscillationSize Q U b L false^2)]
    exact (old_hessian_physical_minus_oscillation m b).trans_eq (by rw [mul_pow,sq_abs])
  have hs := old_hessian_minus_feedback_spatial Q 134 K G P H O κ
    (oldHessianMinusAffineReceiverEnvelope M m b L ω) (β*oldHessianFlatMatrixEnergy M m b L ω)
    (|b| *evalReal scalarRealEnv lowerOscillationExpr) hκ (mul_nonneg (abs_nonneg b) ho)
    (fun U => old_hessian_physical_derivative_kappa m b U.val U.property)
    (fun U => Finset.sum_nonneg (fun _ _ => vectorWeakHaarEnergy_nonneg U.val _))
    (fun U => old_signed_flat_directional_proxy_nonneg Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k b L false) hH (fun _ => Real.sqrt_nonneg _)
    hproxy hHO hOcap
  have hh := old_hessian_actual_minus_feedback_paired_global Q 134 M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 k b L
  dsimp only at hh
  rw [←old_signed_cell_average_eq_descendantsAverage] at hh
  refine ⟨hh.1.mul_left (2*(431/500:ℝ)),?_⟩
  change |∑' n,(2*(431/500:ℝ))*_|≤_
  rw [tsum_mul_left,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2*(431/500))]
  exact (mul_le_mul_of_nonneg_left (hh.2.trans hs) (by norm_num : (0:ℝ)≤2*(431/500))).trans_eq (by
    change (2*(431/500:ℝ))*(κ*(Real.sqrt 2+Real.sqrt (oldHessianParentBottomPairEnergy M m ω))*_)=_
    dsimp only [κ,β,L]
    ring)

end
end ASDExplicitGamma.Scalar
