module

public import ASDExplicitGamma.Native.OldSignedReciprocalSpatialEnergy
public import ASDExplicitGamma.Native.OldSignedQ1WeakContractions

/-! Reciprocal flat energy after both spatial and probability contractions. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Main Triadic Algsuperdiff.Section3
noncomputable section

/-- Deterministic reciprocal energy cap with the actual spatial mesh. -/
def oldSignedQ1ReciprocalSpatialCap (Q : TriadicCube 2) (r : ℕ) (t b : ℝ)
    (L : {l : ℝ // 0<l}) : ℝ :=
  let C := oldSignedQ1PanelHistory t
  let A := 1+2*C+Real.sqrt (2*C)
  let B := (3683/2500:ℝ)
  (cubeScaleFactor Q/3^r*planarC0)^2*mainFlatSigmaSq b L*
    ((B+1)^2*(1+Real.sqrt 2)^2+B*A)

/-- The complete reciprocal oscillation pays the deterministic flat-gradient
cap, with the correlated bank/matrix moment discharged. -/
theorem old_signed_q1_reciprocal_energy_cap
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (r : ℕ) (hr : r=5)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (oldSignedActualReciprocalSpatialEnergy M n r t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualReciprocalSpatialEnergy M n r t b L ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤oldSignedQ1ReciprocalSpatialCap (originCube 2 n) r t b L := by
  have hh := old_signed_q1_reciprocal_spatial_energy M h hM hg n hpast r hr t ht b L
  have hC : 0≤oldSignedQ1PanelHistory t := sq_nonneg _
  have hA : 0≤1+2*oldSignedQ1PanelHistory t+Real.sqrt (2*oldSignedQ1PanelHistory t) :=
    add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hC)) (Real.sqrt_nonneg _)
  have hp := mul_le_mul_of_nonneg_left (old_signed_flat_plus_partition_oscillation_cap
    (originCube 2 n) r b L) (sq_nonneg ((3683/2500:ℝ)+1))
  have hn := mul_le_mul_of_nonneg_left (old_signed_flat_minus_partition_oscillation_cap
    (originCube 2 n) r b L) (mul_nonneg (by norm_num : (0:ℝ)≤3683/2500) hA)
  refine ⟨hh.1,hh.2.trans ((add_le_add hp hn).trans_eq ?_)⟩
  unfold oldSignedQ1ReciprocalSpatialCap
  ring

/-- Mixed OLD-source/reciprocal contraction in the actual correlated law. -/
theorem old_signed_q1_reciprocal_root_contraction
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (fun ω => Real.sqrt (oldSignedActualTiledWeakProxy M n 5 t ω)*
      Real.sqrt (oldSignedActualReciprocalSpatialEnergy M n 5 t b L ω)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,Real.sqrt (oldSignedActualTiledWeakProxy M n 5 t ω)*
      Real.sqrt (oldSignedActualReciprocalSpatialEnergy M n 5 t b L ω)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
        Real.sqrt (theta M*oldSignedQ1PanelXi t)*
          Real.sqrt (oldSignedQ1ReciprocalSpatialCap (originCube 2 n) 5 t b L) := by
  have hw := old_signed_actual_q1_panel_weak M h hM hg n hpast t ht
  have hp := old_signed_q1_reciprocal_energy_cap M h hM hg n hpast 5 rfl t ht b L
  have hh := old_signed_sqrt_product_expectation (Cutoff.cutoffSampleLaw M).toMeasure _ _ hw.1 hp.1
    (old_signed_actual_tiled_weak_proxy_nonneg M n 5 t ht)
    (old_signed_reciprocal_spatial_energy_nonneg M n 5 t b L)
  exact ⟨hh.1,hh.2.trans (mul_le_mul (Real.sqrt_le_sqrt hw.2) (Real.sqrt_le_sqrt hp.2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))⟩

end
end ASDExplicitGamma.Native
