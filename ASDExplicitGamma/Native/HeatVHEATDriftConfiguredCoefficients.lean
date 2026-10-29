module

public import ASDExplicitGamma.Native.HeatVHEATDriftSourceGeometry
public import ASDExplicitGamma.Native.HeatVHEATRefinedCoefficients

/-! Consumption of the proved complete covariance budgets on the actual
refined source geometry. No coefficient certificate is reproved here. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Inverse Variational Numerics.Native
noncomputable section

/-- The actual refined source sums consume the complete q=1 source budgets.
The exact reindexing has already been proved on the physical coefficients. -/
theorem heatVHEATDrift_source_sums_le_configured (n : ℤ) :
    heatVHEATDriftKActual n ≤ (nativeHeatK:ℝ) ∧
    heatVHEATDriftCActual ≤ (nativeHeatM:ℝ) := by
  have hid := heatVHEATDrift_source_sums_eq_refined_row n
  rw [hid.1,hid.2]
  exact nativeHeatQ3RefinedShellCoefficientSums_le

end
end ASDExplicitGamma.Native
