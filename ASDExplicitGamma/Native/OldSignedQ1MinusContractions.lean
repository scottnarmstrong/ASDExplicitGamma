module

public import ASDExplicitGamma.Native.OldSignedMinusSpatialProxy
public import ASDExplicitGamma.Native.OldSignedQ1WeakContractions

/-! The half-trace minus payment in the actual q1 law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Algsuperdiff.Section3
noncomputable section

/-- The separate minus spatial proxy pays half of the panel weak envelope. -/
theorem old_signed_q1_minus_proxy_expectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (oldSignedActualMinusSpatialProxy M n 5 t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualMinusSpatialProxy M n 5 t b L ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤theta M*oldSignedQ1PanelXi t*b^2/2 := by
  have hh := old_signed_minus_spatial_proxy_payment M h hM hg n 5 (by norm_num) t ht hpast b L
  have hb := mul_le_mul_of_nonneg_right (old_signed_q1_source_history_budget M h hM hg n hpast
    (originCube 2 (n-5)) rfl t ht) (sq_nonneg b)
  refine ⟨hh.1,hh.2.trans ?_⟩
  change _≤theta M*oldSignedQ1PanelXi t*b^2/2
  linarith only [hb]

/-- The linear minus derivative term uses the square root of the half-trace
budget, with integrability proved for the actual random profile. -/
theorem old_signed_q1_minus_root_expectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (fun ω => Real.sqrt (oldSignedActualMinusSpatialProxy M n 5 t b L ω))
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,Real.sqrt (oldSignedActualMinusSpatialProxy M n 5 t b L ω)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤Real.sqrt (theta M*oldSignedQ1PanelXi t*b^2/2) := by
  have hp := old_signed_q1_minus_proxy_expectation M h hM hg n hpast t ht b L
  have hh := old_signed_sqrt_expectation (Cutoff.cutoffSampleLaw M).toMeasure _ hp.1
    (old_signed_actual_minus_spatial_proxy_nonneg M n 5 t b L)
  exact ⟨hh.1,hh.2.trans (Real.sqrt_le_sqrt hp.2)⟩

/-- Correlated weak/minus contraction; neither independence nor an estimated
moment is a premise. -/
theorem old_signed_q1_minus_root_contraction
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (fun ω => Real.sqrt (oldSignedActualTiledWeakProxy M n 5 t ω)*
      Real.sqrt (oldSignedActualMinusSpatialProxy M n 5 t b L ω)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,Real.sqrt (oldSignedActualTiledWeakProxy M n 5 t ω)*
      Real.sqrt (oldSignedActualMinusSpatialProxy M n 5 t b L ω)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
        Real.sqrt (theta M*oldSignedQ1PanelXi t)*Real.sqrt (theta M*oldSignedQ1PanelXi t*b^2/2) := by
  have hw := old_signed_actual_q1_panel_weak M h hM hg n hpast t ht
  have hp := old_signed_q1_minus_proxy_expectation M h hM hg n hpast t ht b L
  have hh := old_signed_sqrt_product_expectation (Cutoff.cutoffSampleLaw M).toMeasure _ _ hw.1 hp.1
    (old_signed_actual_tiled_weak_proxy_nonneg M n 5 t ht)
    (old_signed_actual_minus_spatial_proxy_nonneg M n 5 t b L)
  exact ⟨hh.1,hh.2.trans (mul_le_mul (Real.sqrt_le_sqrt hw.2) (Real.sqrt_le_sqrt hp.2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))⟩

end
end ASDExplicitGamma.Native
