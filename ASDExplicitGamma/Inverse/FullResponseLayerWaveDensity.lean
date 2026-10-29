module

public import ASDExplicitGamma.Inverse.FullResponseLayerSpatialHolder

/-! Actual scalar-band and resolution-density pairing on each reset layer. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model

noncomputable section

/-- Every power of a physical resolution field is integrable on its actual
deterministic layer, since it takes only finitely many block values there. -/
theorem layer_resolution_power_integrableOn (M : ABKModel 2) (Q : TriadicCube 2)
    (H0 : ℕ) (hH0 : 333 ≤ H0) (hk : ℕ × ℕ) (τ η : ℝ)
    (e : Fin 3) (ω : Cutoff.CutoffSample 2) (r : ℕ) :
    IntegrableOn (fun x => (layerResolutionDiameter M Q (H0+hk.1) τ η
      (hk.2+1) e ω x)^r) (rootLayerCarrier Q (H0+hk.1) (hk.2+1)) := by
  rw [root_layer_carrier_eq_localization]
  simp only [layerResolutionDiameter, layer_resolution_density_label Q H0 hH0 hk e]
  exact root_block_values_integrableOn Q (resetDensityDepth H0 hk e) _
    (localization_whitney_layer_measurable Q _ _) (localization_whitney_layer_subset Q _ _)
    (fun z => (realDiameterField
      (q3PlanarMarks M (rootFineLabel Q (resetDensityDepth H0 hk e)) τ η) z ω)^r)

/-- The actual spatial density power is its mean budget plus its own positive
excess. This applies to the fourth moment consumed by the wave pairing. -/
theorem layer_resolution_power_average_le_excess
    (M : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 333 ≤ H0)
    (hk : ℕ × ℕ) (τ η q T : ℝ) (e : Fin 3) (ω : Cutoff.CutoffSample 2) (r : ℕ) :
    (∫ x in rootLayerCarrier Q (H0+hk.1) (hk.2+1),
      (layerResolutionDiameter M Q (H0+hk.1) τ η (hk.2+1) e ω x)^r) /
        (volume (cubeSet Q)).toReal ≤
      bankLayerWeight hk.2*densityMomentBudget q r T +
        resetDensityExcess M Q H0 τ η q T r hk e ω := by
  rw [root_layer_carrier_eq_localization]
  simp only [layerResolutionDiameter, layer_resolution_density_label Q H0 hH0 hk e]
  change rootDiameterAverage _ Q (resetDensityDepth H0 hk e) _ r ω ≤ _
  have hh := le_max_left
    (rootDiameterAverage (q3PlanarMarks M
      (rootFineLabel Q (resetDensityDepth H0 hk e)) τ η) Q
        (resetDensityDepth H0 hk e) (localizationWhitneyLayer Q (H0+hk.1) hk.2) r ω -
          bankLayerWeight hk.2*densityMomentBudget q r T) 0
  change _ ≤ resetDensityExcess M Q H0 τ η q T r hk e ω at hh
  linarith only [hh]

/-- Actual later scalar bands and actual density fields satisfy the spatial
pairing with every local integrability premise discharged on every sample. -/
theorem layer_later_band_density_spatial_holder
    (M : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 333 ≤ H0)
    (hk : ℕ × ℕ) (τ η : ℝ) (e : Fin 3) (n J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    let f := laterScalarBand n J weights ω
    let d := layerResolutionDiameter M Q (H0+hk.1) τ η (hk.2+1) e ω
    (∑ U ∈ whitneyRootLayer Q (H0+hk.1) (hk.2+1),
      ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal) *
        ((cubeAverage U f)^2 * cubeAverage U (fun x => d x^2))) ≤
      Real.sqrt (cubeAverage Q (fun x => f x^4)) *
        Real.sqrt ((∫ x in rootLayerCarrier Q (H0+hk.1) (hk.2+1), d x^4)/
          (volume (cubeSet Q)).toReal) := by
  dsimp only
  let f := laterScalarBand n J weights ω
  let d := layerResolutionDiameter M Q (H0+hk.1) τ η (hk.2+1) e ω
  have hf : Continuous f := (later_scalar_band_contDiff n J weights ω).continuous
  have hf4top := continuous_memLp_top_cube Q (normalizedCubeMeasure Q)
    (normalized_cube_support Q) (fun x => f x^4) (hf.pow 4)
  have hf4 : IntegrableOn (fun x => f x^4) (cubeSet Q) :=
    integrableOn_of_integrable_normalizedCubeMeasure Q (hf4top.integrable (by norm_num))
  have hd4 := layer_resolution_power_integrableOn M Q H0 hH0 hk τ η e ω 4
  apply root_layer_wave_density_spatial_holder_root Q (H0+hk.1) hk.2 f d hf4 hd4
  intro U hU
  have hfU := continuous_memLp_top_cube U (normalizedCubeMeasure U)
    (normalized_cube_support U) f hf
  have hf2U := continuous_memLp_top_cube U (normalizedCubeMeasure U)
    (normalized_cube_support U) (fun x => f x^2) (hf.pow 2)
  have hUroot := cubeSet_subset_of_mem_descendantsAtDepth
    (root_whitney_layer_descendants Q (H0+hk.1) (hk.2+1) hU)
  exact ⟨hfU.mono_exponent (by norm_num), hf2U.mono_exponent (by norm_num),
    layer_resolution_density_square_memLp M Q U hUroot H0 hH0 hk τ η e ω⟩

/-- Spatial Holder separates the exact rare mean and the actual positive
density error before any random height is selected. -/
theorem layer_later_band_density_le_mean_add_excess
    (M : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 333 ≤ H0)
    (hk : ℕ × ℕ) (τ η q T : ℝ) (e : Fin 3) (n J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    let f := laterScalarBand n J weights ω
    let d := layerResolutionDiameter M Q (H0+hk.1) τ η (hk.2+1) e ω
    (∑ U ∈ whitneyRootLayer Q (H0+hk.1) (hk.2+1),
      ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal) *
        ((cubeAverage U f)^2 * cubeAverage U (fun x => d x^2))) ≤
      Real.sqrt (cubeAverage Q (fun x => f x^4)) *
        (Real.sqrt (bankLayerWeight hk.2) * Real.sqrt (densityMomentBudget q 4 T) +
          Real.sqrt (resetDensityExcess M Q H0 τ η q T 4 hk e ω)) := by
  dsimp only
  have hh := layer_later_band_density_spatial_holder M Q H0 hH0 hk τ η e n J weights ω
  have hd := layer_resolution_power_average_le_excess M Q H0 hH0 hk τ η q T e ω 4
  have hsadd (a b : ℝ) : Real.sqrt (a+b) ≤ Real.sqrt a+Real.sqrt b := by
    apply (Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))).2
    have ha := (Real.sqrt_le_left (Real.sqrt_nonneg a)).1 (le_refl (Real.sqrt a))
    have hb := (Real.sqrt_le_left (Real.sqrt_nonneg b)).1 (le_refl (Real.sqrt b))
    have hp := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
    nlinarith only [ha, hb, hp]
  have hs := (Real.sqrt_le_sqrt hd).trans (hsadd _ _)
  rw [Real.sqrt_mul (bankLayerWeight_nonneg hk.2)] at hs
  exact hh.trans (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _))

end
end ASDExplicitGamma.Inverse
