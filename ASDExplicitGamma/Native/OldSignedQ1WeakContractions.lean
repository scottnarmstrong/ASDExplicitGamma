module

public import ASDExplicitGamma.Native.OldSignedQ1WeakEnvelope
public import ASDExplicitGamma.Native.OldSignedJointAnnealedContraction

/-! Actual weak and mixed root contractions with the certified q1 envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- The common actual weak root is integrable, with its theta-scaled moment. -/
theorem old_signed_q1_weak_root_expectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    Integrable (fun ω => Real.sqrt (oldSignedActualTiledWeakProxy M n 5 t ω))
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,Real.sqrt (oldSignedActualTiledWeakProxy M n 5 t ω)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤Real.sqrt (theta M*oldSignedQ1PanelXi t) := by
  have hw := old_signed_actual_q1_panel_weak M h hM hg n hpast t ht
  have hh := old_signed_sqrt_expectation (Cutoff.cutoffSampleLaw M).toMeasure _ hw.1
    (old_signed_actual_tiled_weak_proxy_nonneg M n 5 t ht)
  exact ⟨hh.1,hh.2.trans (Real.sqrt_le_sqrt hw.2)⟩

/-- The full joint flat proxy is integrable with the exact physical variance
factor and no separate independence or moment assumption. -/
theorem old_signed_q1_joint_proxy_expectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (oldSignedActualJointSpatialProxy M n 5 t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualJointSpatialProxy M n 5 t b L ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤theta M*oldSignedQ1PanelXi t*b^2 := by
  have hh := old_signed_joint_spatial_proxy_payment M h hM hg n 5 (by norm_num) t ht hpast b L
  have hb := mul_le_mul_of_nonneg_right (old_signed_q1_source_history_budget M h hM hg n hpast
    (originCube 2 (n-5)) rfl t ht) (sq_nonneg b)
  refine ⟨hh.1,hh.2.trans ?_⟩
  convert hb using 1
  ring

/-- The dominant joint affine cross keeps the full theta factor after the
spatial and probability Cauchy--Schwarz contractions. -/
theorem old_signed_q1_joint_root_contraction
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (fun ω => Real.sqrt (oldSignedActualTiledWeakProxy M n 5 t ω)*
      Real.sqrt (oldSignedActualJointSpatialProxy M n 5 t b L ω)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,Real.sqrt (oldSignedActualTiledWeakProxy M n 5 t ω)*
      Real.sqrt (oldSignedActualJointSpatialProxy M n 5 t b L ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤theta M*oldSignedQ1PanelXi t*|b| := by
  have hh := old_signed_joint_annealed_contraction M h hM hg n 5 (by norm_num) t ht hpast b L
  exact ⟨hh.1,hh.2.trans (mul_le_mul_of_nonneg_right
    (old_signed_q1_source_history_budget M h hM hg n hpast (originCube 2 (n-5)) rfl t ht)
      (abs_nonneg b))⟩

end
end ASDExplicitGamma.Native
