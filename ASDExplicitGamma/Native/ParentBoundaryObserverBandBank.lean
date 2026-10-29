module

public import ASDExplicitGamma.Native.ParentBoundaryObserverBandCoefficient
public import ASDExplicitGamma.Inverse.RawShellBandGenerator
public import ASDExplicitGamma.Inverse.FullResponseCoefficientTransport

/-! The actual completed-base observer band as one weighted bank profile.
Old intervening shells have unit weights; every fresh band shell retains sqrt(t). -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The literal old-unit/fresh-attenuated finite weight vector. -/
def parentBoundaryObserverBandWeights (n : ℤ) (t : ℝ) : ℤ → ℝ :=
  sourceBandWeights n (fun _ => Real.sqrt t)

/-- The entire old/fresh attenuation profile stays between zero and one. -/
theorem parent_boundary_observer_band_weights_bounds (q n : ℤ) (height : ℕ) (t : ℝ) (ht : t≤1) :
    ∀ k∈Finset.Ioc q (n+(height:ℤ)),0≤parentBoundaryObserverBandWeights n t k ∧
      parentBoundaryObserverBandWeights n t k≤1 :=
  source_band_weights_bounds q n (n+(height:ℤ)) (fun _ => Real.sqrt t)
    (fun _ _ => ⟨Real.sqrt_nonneg t,Real.sqrt_le_one.mpr ht⟩)

end
end ASDExplicitGamma.Native
