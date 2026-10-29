module

public import ASDExplicitGamma.Inverse.StoppedResolutionFields
public import ASDExplicitGamma.Inverse.StoppedResetDensityFields
public import ASDExplicitGamma.Inverse.WhitneyRootLayerCarrier

/-! Exact physical density resolutions and their positive excesses. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- The geometric three-resolution label is precisely the label of the
source density series, including the physical buffer of forty generations. -/
theorem layer_resolution_density_label (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 333 ≤ H0)
    (hk : ℕ × ℕ) (e : Fin 3) :
    layerResolutionLabel Q (H0+hk.1) (hk.2+1) e=
      rootFineLabel Q (resetDensityDepth H0 hk e) := by
  have he := e.isLt
  unfold layerResolutionLabel compatibleWhitneyMeshDepth whitneyProfile
    rootFineLabel resetDensityDepth localizationResetAbscissa localizationProfileDepth
  omega

/-- Finite actual block populations give spatial integrability for arbitrary
real block values; no probability moment premise is needed. -/
theorem root_block_values_integrableOn (Q : TriadicCube 2) (R : ℕ)
    (E : Set (Vec 2)) (hE : MeasurableSet E) (hEQ : E ⊆ cubeSet Q) (F : BlockSite → ℝ) :
    IntegrableOn (fun x => F (physicalBlockIndex (rootFineLabel Q R) x)) E := by
  apply (integrable_indicator_iff hE).mp
  rw [root_layer_indicator_eq Q R E hEQ F]
  apply integrable_finsetSum
  intro z _
  apply (integrable_indicator_iff (hE.inter (physical_block_set_measurable _ _))).mpr
  exact integrableOn_const (measure_ne_top_of_subset
    (Set.inter_subset_left.trans hEQ) (volume_cubeSet_lt_top Q).ne)

/-- Every actual layer-resolution square is spatially integrable on the
entire deterministic Whitney layer, on every sample. -/
theorem layer_resolution_square_integrableOn (M : ABKModel 2) (Q : TriadicCube 2)
    (H0 : ℕ) (hH0 : 333 ≤ H0) (hk : ℕ × ℕ) (τ η : ℝ) (e : Fin 3) (ω : Cutoff.CutoffSample 2) :
    IntegrableOn (fun x => (layerResolutionDiameter M Q (H0+hk.1) τ η (hk.2+1) e ω x)^2)
      (rootLayerCarrier Q (H0+hk.1) (hk.2+1)) := by
  rw [root_layer_carrier_eq_localization]
  simp only [layerResolutionDiameter,layer_resolution_density_label Q H0 hH0 hk e]
  exact root_block_values_integrableOn Q (resetDensityDepth H0 hk e) _
    (localization_whitney_layer_measurable Q _ _) (localization_whitney_layer_subset Q _ _)
    (fun z => (realDiameterField
      (q3PlanarMarks M (rootFineLabel Q (resetDensityDepth H0 hk e)) τ η) z ω)^2)

/-- The literal geometric density average is bounded by its exact mean
budget plus its actual positive excess, pathwise for every deterministic
height, layer and one of the three resolutions. -/
theorem layer_resolution_average_le_excess (M : ABKModel 2) (Q : TriadicCube 2)
    (H0 : ℕ) (hH0 : 333 ≤ H0) (hk : ℕ × ℕ) (τ η q T : ℝ) (e : Fin 3) (ω : Cutoff.CutoffSample 2) :
    (∫ x in rootLayerCarrier Q (H0+hk.1) (hk.2+1),
      (layerResolutionDiameter M Q (H0+hk.1) τ η (hk.2+1) e ω x)^2)/(volume (cubeSet Q)).toReal ≤
        bankLayerWeight hk.2*densityMomentBudget q 2 T+
          resetDensityExcess M Q H0 τ η q T 2 hk e ω := by
  rw [root_layer_carrier_eq_localization]
  simp only [layerResolutionDiameter,layer_resolution_density_label Q H0 hH0 hk e]
  change rootDiameterAverage _ Q (resetDensityDepth H0 hk e) _ 2 ω ≤ _
  have hh := le_max_left
    (rootDiameterAverage (q3PlanarMarks M (rootFineLabel Q (resetDensityDepth H0 hk e)) τ η)
      Q (resetDensityDepth H0 hk e) (localizationWhitneyLayer Q (H0+hk.1) hk.2) 2 ω-
        bankLayerWeight hk.2*densityMomentBudget q 2 T) 0
  change _ ≤ resetDensityExcess M Q H0 τ η q T 2 hk e ω at hh
  linarith only [hh]

end
end ASDExplicitGamma.Inverse
