module

public import ASDExplicitGamma.Scalar.OldHessianTrialPrincipalLocal
public import ASDExplicitGamma.Scalar.OldHessianTrialCertifiedTraceMoments
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedHistoryAdapter

/-! The actual principal signed covariance pays the full fine trace once. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section

/-- The actual local TOP receiver in the principal covariance after the
genuine global parent-gradient cancellation; local jumps are retained. -/
def oldHessianPrincipalSpatialCross (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) : ℝ :=
  let u := oldHessianMixedPotential Q coarse nu sigma hnu hsigma k
  let a := responseFramePlanarCoefficientField nu sigma k
  let G := fun i : Fin 2 => fun x => (scalarCoefficientFlux a
    (oldSignedLocalResidual Q (coarse+1) nu sigma hnu hsigma k
      (fun _ => (basisVec i,0)) (memLp_const (basisVec i,0))) x).2
  ∑ i : Fin 2,cubeAverage Q (fun x => vecDot (oldHessianRotatedReceiver G i x)
    ((diagInterpolant Q (coarse+1) (u i).toH1Function).grad x))

/-- The complete genuine principal pairing has the proved one-half
fine-history/full-fine-trace payment before expectation. -/
theorem old_hessian_principal_spatial_half (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    |oldHessianPrincipalSpatialCross Q coarse nu sigma hnu hsigma k|≤
      oldHessianFineInverseHistory Q (coarse+1) nu sigma k*
        descendantsAverage Q (coarse+1) (fun U =>
          traceDefect (openCubeSet U) (responseFramePlanarCoefficientField nu sigma k) 1)/2 :=
  old_hessian_actual_local_principal_half Q coarse nu sigma hnu hsigma k

/-- Nonnegative integrable principal covariance majorant. -/
def oldHessianThirdBill (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ := ((431/500:ℝ)*b^2/2)*
      (oldHessianGroupedBank M m ω*oldHessianSourceTrace M m 5 ω)

/-- The actual principal covariance costs exactly lambda X5²/2. The
coarse bottom and fine top energies have already been combined into one
full fine trace, and the scalar-grouped reserve is kept in X5². -/
theorem old_hessian_actual_third_bill
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    Integrable (oldHessianThirdBill M m b) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        |((431/500:ℝ)*b^2)*oldHessianPrincipalSpatialCross (originCube 2 (m+129)) 133 M.nu
          (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1
          (oldHessianOldOpenCoefficient (m+129) m ω)|≤oldHessianThirdBill M m b ω) ∧
      (∫ ω,oldHessianThirdBill M m b ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
        b^2*evalReal scalarRealEnv lowerTerm3Expr := by
  have ht := old_hessian_actual_certified_trace_moments M h hM hg N hpast m hm
  have hc : 0≤(431/500:ℝ)*b^2/2 := by positivity
  refine ⟨ht.2.2.1.const_mul _,?_,?_⟩
  · filter_upwards [old_hessian_actual_fine_histories_le_bank M h hM hg N hpast m hm] with ω hbank
    let Q := originCube 2 (m+129)
    let k := oldHessianOldOpenCoefficient (m+129) m ω
    have hp := old_hessian_principal_spatial_half Q 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k
    have hcap := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hbank 5 (by norm_num))
      (old_hessian_source_trace_nonneg M m 5 ω)) (by norm_num : (0:ℝ)≤2)
    have hP : |oldHessianPrincipalSpatialCross Q 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1 k|≤
        (oldHessianGroupedBank M m ω*oldHessianSourceTrace M m 5 ω)/2 := hp.trans hcap
    have hc' : 0≤(431/500:ℝ)*b^2 := mul_nonneg (by norm_num) (sq_nonneg b)
    rw [abs_mul,abs_of_nonneg hc']
    exact (mul_le_mul_of_nonneg_left hP hc').trans_eq (by unfold oldHessianThirdBill; ring)
  · change (∫ ω,((431/500:ℝ)*b^2/2)*(oldHessianGroupedBank M m ω*oldHessianSourceTrace M m 5 ω)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤_
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left ht.2.2.2.1 hc).trans_eq (by
      norm_num only [lowerTerm3Expr,evalReal,sc]
      ring)

end
end ASDExplicitGamma.Scalar
