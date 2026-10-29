module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetOrbitGaussian
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetBandStrongDerivative
public import ASDExplicitGamma.Scalar.UpperCellEnergyBandGaussian

/-! Gaussianity of the source-sign potential correction. The complete Gaussian
orbit is preserved by the actual stationary projection; no independence between
the projected field and its forcing is used. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ProbabilityTheory
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
open Algsuperdiff.Section3 Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec 2) Ω]
variable {μ : Measure Ω}
variable [MeasurableConstVAdd (Vec 2) Ω] [VAddInvariantMeasure (Vec 2) Ω μ]

/-- The actual source-sign potential correction stays in the scalar forcing's
closed Gaussian orbit, coordinate by coordinate. -/
theorem upper_cell_potential_orbit_mem
    (v : ScalarL2 μ) (F : VectorL2 2 μ)
    (hF : ∀ i, vectorL2Coord i F ∈ upperCellResetOrbit v) (i : Fin 2) :
    vectorL2Coord i (-stationaryPotentialProjection F) ∈ upperCellResetOrbit v := by
  have hs := (upperCellResetOrbit v).sub_mem
    (upper_cell_reset_flux_orbit_mem v F hF i) (hF i)
  rw [←map_sub] at hs
  have he : upperCellResetStationaryFlux F-F = -stationaryPotentialProjection F := by
    change (F-stationaryPotentialProjection F)-F = _
    abel
  rwa [he] at hs

/-- Centered Gaussianity of the genuine potential correction follows from the
joint forcing orbit law, including its correlations with the forcing. -/
theorem upper_cell_potential_orbit_gaussian [IsProbabilityMeasure μ]
    (v : ScalarL2 μ)
    (hv : IsCenteredGaussianFamily μ (fun z : Vec 2 => fun ω => koopman z v ω))
    (F : VectorL2 2 μ)
    (hF : ∀ i, vectorL2Coord i F ∈ upperCellResetOrbit v) (i : Fin 2) :
    ∃ variance : NNReal, μ.map (vectorL2Coord i (-stationaryPotentialProjection F)) =
      gaussianReal 0 variance :=
  upper_cell_reset_gaussian_closed_span μ (fun z : Vec 2 => koopman z v) hv _
    (upper_cell_potential_orbit_mem v F hF i)

/-- The physical finite-band orbit law needed by both potential and flux
projections, with the Gaussian producer discharged from the model law. -/
theorem upper_cell_band_orbit_gaussian {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ) :
    IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
      (fun z : Vec 2 => fun ω => koopman z
        (upperCellResetBandJetClass M k w
          (upper_cell_band_jets_gaussian M h hM k hk w) (.value 0)) ω) :=
  upper_cell_reset_band_orbit_gaussian M k w
    (upper_cell_band_jets_gaussian M h hM k hk w)

end
end ASDExplicitGamma.Scalar
