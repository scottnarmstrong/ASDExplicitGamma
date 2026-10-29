module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalPotentialGaussian
public import Algsuperdiff.Section3.Provider.Corrector.ShellSumEnergyDisplay

/-! Exact energy of the actual full-band potential correction, using orthogonal
shell decomposition and the proved q3 value of the canonical J4 constant. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
open Algsuperdiff.Section3 Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Model
noncomputable section

/-- Transport to the original cutoff law preserves the potential correction's
exact energy, including its source sign and direction normalization. -/
theorem upper_cell_potential_energy_transport
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2) :
    ‖-stationaryPotentialProjection (upperCellResetBandForcing M n terminal c e)‖^2 =
      ∫ f, ‖shellSumCorrectorRepr M (c • e) n terminal f‖^2
        ∂(shellSumValuePathLaw M.P n terminal).toMeasure := by
  let hp := measurePreserving_shellSumValuePath_cutoffSample M n terminal
  have hequiv (x : Vec 2) (ω : Cutoff.CutoffSample 2) :
      shellSumValuePath n terminal (x +ᵥ ω).val = x +ᵥ shellSumValuePath n terminal ω.val :=
    shellSumValuePath_translateSequence n terminal x ω.val
  rw [integral_normSq_shellSumCorrectorRepr_eq_norm_sq]
  change ‖-stationaryPotentialProjection (carrierTransport (HilbertVec 2) hp
    (shellSumForcingL2 M (c • e) n terminal))‖^2 =
      ‖-stationaryPotentialProjection (shellSumForcingL2 M (c • e) n terminal)‖^2
  rw [stationaryPotentialProjection_carrierTransport hp hequiv,norm_neg,norm_neg,
    norm_carrierTransport]

/-- Exact full-band projected variance on the physical cutoff carrier. The
factor one half is the q3 potential-projection energy, not a contraction bound. -/
theorem upper_cell_potential_variance
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n terminal : ℤ) (c : ℝ) {e : Vec 2} (he : Book.Ch02.vecNorm e = 1) :
    ‖-stationaryPotentialProjection (upperCellResetBandForcing M n terminal c e)‖^2 =
      c^2 * (h^2/2) * ∑ k ∈ Finset.Ioc n terminal, (3:ℝ)^(2*M.gamma*(k:ℝ)) := by
  rw [upper_cell_potential_energy_transport,
    integral_normSq_shellSumCorrectorRepr_gauge_display M c he,q3_cstar_exact M h hM]
  have hl : Real.log (3:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp

end
end ASDExplicitGamma.Scalar
