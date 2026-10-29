module

public import ASDExplicitGamma.Inverse.ClippedMatrix
public import ASDExplicitGamma.Inverse.PhysicalGaussianCorrelatedDensity
public import ASDExplicitGamma.Inverse.PhysicalWave

/-! Correlated wave errors, retaining the density at order p. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The three density excesses are actual measurable root observables. -/
theorem root_density_excess_measurable (M : ABKModel 2) (Q : TriadicCube 2)
    (H i : ℕ) (e : Fin 3) (m : ℕ) :
    Measurable (rootLayerDensityExcess M Q H i e m) := by
  let j := Q.scale - (layerDepth H i : ℤ)
  let B := q3PlanarMarks M j resetAllOrderTau (waveGateEta .allOrder)
  have hX := root_diameter_average_measurable B
    (q3_local_mark_measurable M j resetAllOrderTau (waveGateEta .allOrder))
    (q3_positive_mark_measurable M j resetAllOrderTau (waveGateEta .allOrder))
    Q (layerDepth H i-40-e.val) (localizationWhitneyLayer Q H (i-1))
    (localization_whitney_layer_measurable Q H (i-1))
    (localization_whitney_layer_subset Q H (i-1)) m
  exact (hX.sub measurable_const).max measurable_const

end
end ASDExplicitGamma.Inverse
