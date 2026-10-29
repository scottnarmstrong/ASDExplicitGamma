module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandForcingCoordinates
public import ASDExplicitGamma.Scalar.UpperCellEnergyPotentialGaussian
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Centered Gaussian laws for the actual full-band potential correction and
its spatial averages. The forcing/orbit premises are discharged here. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ProbabilityTheory
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
open Algsuperdiff.Section3 Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
noncomputable section

/-- Every physical forcing coordinate is in the complete scalar band orbit. -/
theorem upper_cell_physical_forcing_orbit_mem
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (c : ℝ) (e : Vec 2) (i : Fin 2) :
    vectorL2Coord i (upperCellResetBandForcing M n (n+height) c e) ∈
      upperCellResetOrbit
        (upperCellResetBandJetClass M (upperCellPhysicalBandLabel n height)
          (fun _ => c) (upper_cell_band_jets_gaussian M h hM _
            (upper_cell_physical_band_label_injective n height) _) (.value 0)) := by
  rw [upper_cell_band_forcing_coord M h hM]
  apply Submodule.smul_mem
  apply subset_closure
  apply Submodule.subset_span
  exact ⟨0,koopman_zero _⟩

/-- Actual full-band potential correction coordinates have centered Gaussian
laws. Only the model law is assumed; no estimate or Gaussian optimizer premise. -/
theorem upper_cell_physical_potential_gaussian
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (c : ℝ) (e : Vec 2) (i : Fin 2) :
    ∃ variance : NNReal,
      (Cutoff.cutoffSampleLaw M).toMeasure.map
        (vectorL2Coord i (-stationaryPotentialProjection
          (upperCellResetBandForcing M n (n+height) c e))) = gaussianReal 0 variance := by
  exact upper_cell_potential_orbit_gaussian _
    (upper_cell_band_orbit_gaussian M h hM _
      (upper_cell_physical_band_label_injective n height) (fun _ => c)) _
    (upper_cell_physical_forcing_orbit_mem M h hM n height c e) i

end
end ASDExplicitGamma.Scalar
