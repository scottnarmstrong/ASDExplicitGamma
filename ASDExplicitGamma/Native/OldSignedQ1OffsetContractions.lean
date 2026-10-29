module

public import ASDExplicitGamma.Native.OldSignedReciprocalOffsetEnergy
public import ASDExplicitGamma.Native.OldSignedQ1WeakContractions

/-! Sharp offset roots used in the OLD reciprocal derivative feedback. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Algsuperdiff.Section3
noncomputable section

/-- The reciprocal derivative offset root retains its exact coefficient. -/
theorem old_signed_q1_offset_root_expectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let C := oldSignedQ1PanelHistory t
    let A := 1+2*C+Real.sqrt (2*C)
    let om := descendantsAverage (originCube 2 n) 5 (fun U => oldSignedFlatOscillationSize (originCube 2 n) U b L false^2)
    Integrable (fun ω => Real.sqrt (oldSignedActualReciprocalOffsetEnergy M n 5 t b L ω))
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,Real.sqrt (oldSignedActualReciprocalOffsetEnergy M n 5 t b L ω)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤(Real.sqrt ((3683/2500:ℝ)*A)+1)*Real.sqrt om := by
  intro C A om
  have he := old_signed_q1_reciprocal_offset_energy M h hM hg n hpast 5 rfl t ht b L
  have hh := old_signed_sqrt_expectation (Cutoff.cutoffSampleLaw M).toMeasure _ he.1
    (old_signed_reciprocal_offset_energy_nonneg M n 5 t b L)
  refine ⟨hh.1,hh.2.trans ((Real.sqrt_le_sqrt he.2).trans_eq ?_)⟩
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (by norm_num))]

/-- The reciprocal offset paired with the same actual weak history is
contracted in the common law, without independence. -/
theorem old_signed_q1_offset_root_contraction
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let C := oldSignedQ1PanelHistory t
    let A := 1+2*C+Real.sqrt (2*C)
    let om := descendantsAverage (originCube 2 n) 5 (fun U => oldSignedFlatOscillationSize (originCube 2 n) U b L false^2)
    Integrable (fun ω => Real.sqrt (oldSignedActualTiledWeakProxy M n 5 t ω)*
      Real.sqrt (oldSignedActualReciprocalOffsetEnergy M n 5 t b L ω)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,Real.sqrt (oldSignedActualTiledWeakProxy M n 5 t ω)*
      Real.sqrt (oldSignedActualReciprocalOffsetEnergy M n 5 t b L ω)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
        Real.sqrt (theta M*oldSignedQ1PanelXi t)*((Real.sqrt ((3683/2500:ℝ)*A)+1)*Real.sqrt om) := by
  intro C A om
  have hw := old_signed_actual_q1_panel_weak M h hM hg n hpast t ht
  have he := old_signed_q1_reciprocal_offset_energy M h hM hg n hpast 5 rfl t ht b L
  have hh := old_signed_sqrt_product_expectation (Cutoff.cutoffSampleLaw M).toMeasure _ _ hw.1 he.1
    (old_signed_actual_tiled_weak_proxy_nonneg M n 5 t ht)
    (old_signed_reciprocal_offset_energy_nonneg M n 5 t b L)
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hc : Real.sqrt (∫ ω,oldSignedActualReciprocalOffsetEnergy M n 5 t b L ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤(Real.sqrt ((3683/2500:ℝ)*A)+1)*Real.sqrt om := by
    apply (Real.sqrt_le_sqrt he.2).trans_eq
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (by norm_num))]
  exact mul_le_mul (Real.sqrt_le_sqrt hw.2) hc (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end ASDExplicitGamma.Native
