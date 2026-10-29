module

public import Algsuperdiff.Section3.Provider.Corrector.MollifiedDecorrelation

/-! Translation and derivative transport through the actual stationary
Helmholtz projection used to construct the full RESET band flux. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Probability.Stationary
open Algsuperdiff.Section3.Provider.Corrector
noncomputable section

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω}
variable [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ]

/-- The actual stationary potential projection commutes with translations. -/
theorem upper_cell_reset_potential_translate (z : Vec d) (F : VectorL2 d μ) :
    stationaryPotentialProjection (koopman z F)=koopman z (stationaryPotentialProjection F) := by
  symm
  apply eq_stationaryPotentialProjection_of_mem_of_sub_mem_orthogonal
  · exact koopman_mem_stationaryPotentialSubspace z (stationaryPotentialProjection_mem F)
  · rw [←map_sub]
    exact koopman_mem_stationarySolenoidalSubspace z
      (sub_stationaryPotentialProjection_mem_orthogonal F)

/-- The full flux is the literal orthogonal solenoidal projection. -/
def upperCellResetStationaryFlux : VectorL2 d μ →L[ℝ] VectorL2 d μ :=
  ContinuousLinearMap.id ℝ _-stationaryPotentialProjection

/-- The full stationary flux projection is a contraction, with constant one. -/
theorem upper_cell_reset_stationary_flux_norm (F : VectorL2 d μ) :
    ‖upperCellResetStationaryFlux F‖ ≤ ‖F‖ := by
  have hh := (stationaryPotentialSubspace (μ := μ) (d := d))ᗮ.norm_starProjection_apply_le F
  rw [Submodule.starProjection_orthogonal_val] at hh
  exact hh

/-- The full stationary flux projection commutes with translations. -/
theorem upper_cell_reset_flux_translate (z : Vec d) (F : VectorL2 d μ) :
    upperCellResetStationaryFlux (koopman z F)=koopman z (upperCellResetStationaryFlux F) := by
  change koopman z F-stationaryPotentialProjection (koopman z F)=_
  rw [upper_cell_reset_potential_translate]
  exact (map_sub (koopman z) F (stationaryPotentialProjection F)).symm

/-- A genuine strong horizontal derivative passes through the full flux
projection. No derivative regularity is assumed on the corrected field. -/
theorem upper_cell_reset_flux_derivative (b : Vec d) (F D : VectorL2 d μ)
    (hD : HasDerivAt (fun t : ℝ => koopman (t • b) F) D 0) :
    HasDerivAt (fun t : ℝ => koopman (t • b) (upperCellResetStationaryFlux F))
      (upperCellResetStationaryFlux D) 0 := by
  have hd := (upperCellResetStationaryFlux (μ := μ)).hasFDerivAt.comp_hasDerivAt 0 hD
  simpa only [Function.comp_def,upper_cell_reset_flux_translate] using hd

end
end ASDExplicitGamma.Scalar
