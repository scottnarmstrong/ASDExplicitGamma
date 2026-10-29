module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetStationaryProjection
public import ASDExplicitGamma.Scalar.CutoffStream
public import Algsuperdiff.Section3.Provider.Corrector.StationaryCarrierTransport

/-! Identification of the actual full flux with the stationary solenoidal
projection on the original cutoff carrier, retaining all band shells. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
open Algsuperdiff.Frozen.Assumptions
noncomputable section

/-- The actual finite-band forcing pulled to the original cutoff law. -/
def upperCellResetBandForcing (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2) :
    VectorL2 2 (Cutoff.cutoffSampleLaw M).toMeasure :=
  carrierTransport (HilbertVec 2) (measurePreserving_shellSumValuePath_cutoffSample M n terminal)
    (shellSumForcingL2 M (c • e) n terminal)

/-- The actual shell-sum flux is its forcing's orthogonal solenoidal projection
on the shell-sum carrier. -/
theorem upper_cell_reset_shell_sum_projection (M : ABKModel 2) (e : Vec 2) (n terminal : ℤ) :
    (memLp_two_shellSumFlux M e n terminal).toLp (shellSumFlux M e n terminal)=
      upperCellResetStationaryFlux (shellSumForcingL2 M e n terminal) := by
  rw [show (memLp_two_shellSumFlux M e n terminal).toLp (shellSumFlux M e n terminal)=
      shellSumForcingL2 M e n terminal+
        (memLp_two_shellSumCorrectorRepr M e n terminal).toLp
          (shellSumCorrectorRepr M e n terminal) from
    MemLp.toLp_add (memLp_two_valuePathForcing_shellSum M e n terminal)
      (memLp_two_shellSumCorrectorRepr M e n terminal),toLp_shellSumCorrectorRepr]
  change shellSumForcingL2 M e n terminal+ -stationaryPotentialProjection
    (shellSumForcingL2 M e n terminal)=shellSumForcingL2 M e n terminal-
      stationaryPotentialProjection (shellSumForcingL2 M e n terminal)
  exact (sub_eq_add_neg _ _).symm

/-- The physical full flux equals the literal solenoidal projection on
the cutoff law. No first-chaos or gradient/moment hypothesis is added. -/
theorem upper_cell_reset_band_projection
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2) :
    (memLp_two_cutoffBandFlux M n terminal c e).toLp (cutoffBandFlux M n terminal c e)=
      upperCellResetStationaryFlux (upperCellResetBandForcing M n terminal c e) := by
  let hp := measurePreserving_shellSumValuePath_cutoffSample M n terminal
  have hequiv (x : Vec 2) (ω : Cutoff.CutoffSample 2) :
      shellSumValuePath n terminal (x +ᵥ ω).val=x +ᵥ shellSumValuePath n terminal ω.val :=
    shellSumValuePath_translateSequence n terminal x ω.val
  have ht : (memLp_two_cutoffBandFlux M n terminal c e).toLp (cutoffBandFlux M n terminal c e)=
      carrierTransport (HilbertVec 2) hp
        ((memLp_two_shellSumFlux M (c • e) n terminal).toLp (shellSumFlux M (c • e) n terminal)) := rfl
  rw [ht,upper_cell_reset_shell_sum_projection]
  change carrierTransport (HilbertVec 2) hp
      (shellSumForcingL2 M (c • e) n terminal-stationaryPotentialProjection
        (shellSumForcingL2 M (c • e) n terminal))=_
  rw [map_sub,←stationaryPotentialProjection_carrierTransport hp hequiv]
  rfl

/-- A derivative of the actual uncorrected band transports to the genuine
corrected flux, with the same solenoidal projection on its derivative. -/
theorem upper_cell_reset_band_derivative
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e b : Vec 2)
    (D : VectorL2 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hD : HasDerivAt (fun t : ℝ => koopman (t • b)
      (upperCellResetBandForcing M n terminal c e)) D 0) :
    HasDerivAt (fun t : ℝ => koopman (t • b)
      ((memLp_two_cutoffBandFlux M n terminal c e).toLp (cutoffBandFlux M n terminal c e)))
        (upperCellResetStationaryFlux D) 0 := by
  rw [upper_cell_reset_band_projection]
  exact upper_cell_reset_flux_derivative b _ D hD

end
end ASDExplicitGamma.Scalar
