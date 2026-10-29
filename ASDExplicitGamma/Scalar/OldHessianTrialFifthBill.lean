module

public import ASDExplicitGamma.Scalar.OldHessianTrialFlatBills
public import ASDExplicitGamma.Scalar.OldHessianTrialCovarianceReceiver
public import ASDExplicitGamma.Scalar.OldHessianTrialActualCovarianceReceiver
public import ASDExplicitGamma.Scalar.OldHessianTrialCovarianceSpatial
public import ASDExplicitGamma.Scalar.OldHessianTrialFrozenErrorFrobenius
public import ASDExplicitGamma.Scalar.OldHessianTrialSourceBank

/-! Fifth OLD bill: the finite-parent covariance error cross. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Correlated source/covariance-error envelope of the fifth bill. -/
def oldHessianFifthBill (M : ABKModel 2) (m : ℤ) (b : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (2*(431/500:ℝ))*(Real.sqrt (oldHessianGroupedBank M m ω*oldHessianSourceTrace M m 4 ω)*
    Real.sqrt (oldHessianCovarianceReceiverEnvelope M m b (q3ModelLength (m+1)) ω))

/-- The Frobenius covariance-error root is at most `b² ē`. -/
theorem old_hessian_physical_covariance_error_root (m : ℤ) (b : ℝ) (hb : 0<b) :
    Real.sqrt (oldSignedCellAverage (originCube 2 (m+129)) 134
      (fun U => oldHessianCovarianceErrorCellEnergy (originCube 2 (m+129)) U.val b (q3ModelLength (m+1))))≤
      b^2*evalReal scalarRealEnv lowerEbarExpr := by
  let Q := originCube 2 (m+129)
  let L := q3ModelLength (m+1)
  let r := cubeScaleFactor Q/(3:ℝ)^134
  rw [old_signed_cell_average_eq_descendantsAverage Q 134
    (fun U => oldHessianCovarianceErrorCellEnergy Q U b L)]
  refine (old_hessian_covariance_error_frobenius Q 134 b L).trans ?_
  have hB := old_hessian_physical_flat_boundary m b hb
  have hroot : Real.sqrt (oldSignedFlatBoundaryEnergy Q b L/2)≤
      b*Real.sqrt (evalReal scalarRealEnv lowerFlatTailExpr/2) := by
    have hh := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hB (by norm_num : (0:ℝ)≤2))
    rw [mul_div_assoc,Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq hb.le] at hh
    exact hh
  have hs : Real.sqrt (mainFlatSigmaSq b L)=b*Real.sqrt (156/5:ℝ)/L.val := by
    have he : mainFlatSigmaSq b L=b^2*(156/5:ℝ)/L.val^2 := by unfold mainFlatSigmaSq; ring
    rw [he,Real.sqrt_div (mul_nonneg (sq_nonneg b) (by norm_num)),
      Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq hb.le,Real.sqrt_sq L.property.le]
  have hr : r/L.val=1/(3:ℝ)^6 := old_hessian_physical_mesh_ratio m 5
  have he : r*Real.sqrt (mainFlatSigmaSq b L)=b*evalReal scalarRealEnv lowerS1Expr := by
    rw [hs]
    calc
      _ = b*Real.sqrt (156/5:ℝ)*(r/L.val) := by ring
      _ = _ := by rw [hr]; norm_num [evalReal,lowerS1Expr,sc]; ring
  have hosc : Real.sqrt (descendantsAverage Q 134 (fun U =>
      oldSignedFlatOscillationSize Q U b L false^2))≤b*evalReal scalarRealEnv lowerOscillationExpr := by
    have hh := Real.sqrt_le_sqrt (old_hessian_physical_minus_oscillation m b)
    rw [Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq hb.le,
      Real.sqrt_sq (by norm_num [evalReal,lowerOscillationExpr,lowerS1Expr,sc])] at hh
    exact hh
  have hpi : 1/Real.pi≤(319/1000:ℝ) := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_d2]
  have hS : 0≤evalReal scalarRealEnv lowerS1Expr := by norm_num [evalReal,lowerS1Expr,sc]
  have hO : 0≤evalReal scalarRealEnv lowerOscillationExpr := by
    norm_num [evalReal,lowerOscillationExpr,lowerS1Expr,sc]
  have h2 : r/Real.pi*Real.sqrt (mainFlatSigmaSq b L)*
      Real.sqrt (descendantsAverage Q 134 (fun U => oldSignedFlatOscillationSize Q U b L false^2))≤
      b^2*((319/1000:ℝ)*evalReal scalarRealEnv lowerS1Expr*evalReal scalarRealEnv lowerOscillationExpr) := by
    have e1 : r/Real.pi*Real.sqrt (mainFlatSigmaSq b L)=(1/Real.pi)*(b*evalReal scalarRealEnv lowerS1Expr) := by
      rw [←he]; ring
    rw [e1]
    have h3 : (1/Real.pi)*(b*evalReal scalarRealEnv lowerS1Expr)≤(319/1000:ℝ)*(b*evalReal scalarRealEnv lowerS1Expr) :=
      mul_le_mul_of_nonneg_right hpi (mul_nonneg hb.le hS)
    calc _ ≤ ((319/1000:ℝ)*(b*evalReal scalarRealEnv lowerS1Expr))*
          (b*evalReal scalarRealEnv lowerOscillationExpr) :=
          mul_le_mul h3 hosc (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  have h1 : |b| *Real.sqrt (oldSignedFlatBoundaryEnergy Q b L/2)≤b^2*Real.sqrt (evalReal scalarRealEnv lowerFlatTailExpr/2) := by
    rw [abs_of_pos hb]
    calc _ ≤ b*(b*Real.sqrt (evalReal scalarRealEnv lowerFlatTailExpr/2)) :=
          mul_le_mul_of_nonneg_left hroot hb.le
      _ = _ := by ring
  have := add_le_add h1 h2
  refine this.trans_eq ?_
  simp only [lowerEbarExpr,evalReal,sc]
  ring

/-- Fifth bill: the finite-parent covariance cross has its source/root envelope,
whose moment is `b² * lowerTerm5Expr`. -/
theorem old_hessian_actual_fifth_bill
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) (hb : 0<b) :
    Integrable (oldHessianFifthBill M m b) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      |(2*(431/500:ℝ))*oldHessianCovarianceSpatialCross (originCube 2 (m+129)) 133 M.nu
        (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1
        (oldHessianOldOpenCoefficient (m+129) m ω) b (q3ModelLength (m+1))|≤
        oldHessianFifthBill M m b ω) ∧
    (∫ ω,oldHessianFifthBill M m b ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      b^2*evalReal scalarRealEnv lowerTerm5Expr := by
  let L := q3ModelLength (m+1)
  obtain ⟨hi,hint⟩ := old_hessian_covariance_receiver_root_payment M h hM hg N hpast m hm b L
  refine ⟨hi.const_mul _,?_,?_⟩
  · filter_upwards [old_hessian_actual_source_components_bank M h hM hg N hpast m hm,
      old_hessian_actual_covariance_receiver_energy M h hM hg N hpast m hm b L] with ω hω hr
    have hp := old_hessian_covariance_spatial_pairing (originCube 2 (m+129)) 133 M.nu
      (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1
      (oldHessianOldOpenCoefficient (m+129) m ω) b L
    have h1 := Real.sqrt_le_sqrt hω.1
    have h2 := Real.sqrt_le_sqrt hr
    have h3 := hp.trans (mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2*(431/500))]
    exact mul_le_mul_of_nonneg_left h3 (by norm_num)
  · change (∫ ω,(2*(431/500:ℝ))*(Real.sqrt (oldHessianGroupedBank M m ω*oldHessianSourceTrace M m 4 ω)*
      Real.sqrt (oldHessianCovarianceReceiverEnvelope M m b L ω)) ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤_
    rw [integral_const_mul]
    have hX : 0≤evalReal scalarRealEnv lowerX4Expr := by
      simp only [lowerX4Expr,evalReal]; exact Real.sqrt_nonneg _
    have hXi : 0≤Real.sqrt (evalReal scalarRealEnv lowerXiExpr/2) := Real.sqrt_nonneg _
    have hroot := old_hessian_physical_covariance_error_root m b hb
    have hh := hint.trans (mul_le_mul_of_nonneg_left hroot (mul_nonneg hX hXi))
    apply (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤2*(431/500))).trans_eq
    have hxi : Real.sqrt (evalReal scalarRealEnv lowerXiExpr/2)=
        Real.sqrt (evalReal scalarRealEnv lowerXiExpr*2)/2 := by
      have h0 : 0≤evalReal scalarRealEnv lowerXiExpr := by norm_num [evalReal,lowerXiExpr,sc]
      rw [show evalReal scalarRealEnv lowerXiExpr/2=(evalReal scalarRealEnv lowerXiExpr*2)/2^2 by ring,
        Real.sqrt_div (by positivity),Real.sqrt_sq (by norm_num : (0:ℝ)≤2)]
    rw [hxi]
    simp only [lowerTerm5Expr,evalReal,sc]
    ring

end
end ASDExplicitGamma.Scalar
