module

public import ASDExplicitGamma.Native.OldSignedBoundarySpatialPayment
public import ASDExplicitGamma.Native.OldSignedQ1WeakContractions

/-! Annealed covariance-boundary payment for the actual OLD partition. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Main Triadic Algsuperdiff.Section3
noncomputable section

/-- The full covariance boundary envelope after the sharp spatial contraction. -/
def oldSignedActualBoundaryEnvelope (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 n
  let C := b^2+3*(cubeScaleFactor Q/3^r)*planarC1*|b| *Real.sqrt (mainFlatSigmaSq b L)
  let W := oldSignedActualTiledWeakProxy M n r t ω
  2*C*(Real.sqrt W+Real.sqrt (2*W))

/-- Both covariance boundary terms are paid by the actual q1 weak moment,
including the integrability needed in the signed generator return. -/
theorem old_signed_q1_boundary_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let C := b^2+3*(cubeScaleFactor Q/3^5)*planarC1*|b| *Real.sqrt (mainFlatSigmaSq b L)
    let X := theta M*oldSignedQ1PanelXi t
    Integrable (oldSignedActualBoundaryEnvelope M n 5 t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualBoundaryEnvelope M n 5 t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      2*C*(Real.sqrt X+Real.sqrt (2*X)) := by
  intro Q C X
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let W := oldSignedActualTiledWeakProxy M n 5 t
  have hw := old_signed_actual_q1_panel_weak M h hM hg n hpast t ht
  have hr := old_signed_q1_weak_root_expectation M h hM hg n hpast t ht
  have htwo := old_signed_sqrt_expectation μ (fun ω => 2*W ω) (hw.1.const_mul 2)
    (fun ω => mul_nonneg (by norm_num) (old_signed_actual_tiled_weak_proxy_nonneg M n 5 t ht ω))
  have htwocap : (∫ ω,Real.sqrt (2*W ω) ∂μ)≤Real.sqrt (2*X) := by
    apply htwo.2.trans
    apply Real.sqrt_le_sqrt
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hw.2 (by norm_num)
  refine ⟨(hr.1.add htwo.1).const_mul _,?_⟩
  change (∫ ω,2*C*(Real.sqrt (W ω)+Real.sqrt (2*W ω)) ∂μ)≤_
  rw [integral_const_mul,integral_add hr.1 htwo.1]
  have hC : 0≤C := add_nonneg (sq_nonneg b)
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg (Triadic.cubeScaleFactor_pos' Q).le (by positivity))) (Real.sqrt_nonneg _))
        (abs_nonneg b)) (Real.sqrt_nonneg _))
  exact mul_le_mul_of_nonneg_left (add_le_add hr.2 htwocap) (mul_nonneg (by norm_num) hC)

end
end ASDExplicitGamma.Native
