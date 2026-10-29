module

public import ASDExplicitGamma.Scalar.UpperCellEnergyProjectedTriangle

/-! Transfer the proved Hilbert projection payment to the same physical trial. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Algsuperdiff.Section3
noncomputable section

/-- For any measurable genuine band-load representative, construct a physical
zero-trace/zero-normal-trace correction with exactly its projected energy.
The construction uses this F, so principal and RESET payments apply to the
same trial rather than unrelated existential witnesses. -/
theorem upper_cell_trial_from_load
    (M : ABKModel 2) (n terminal : ℤ) (sigma : ℝ) (hsigma : 0<sigma)
    (e : Vec 2) (Q : TriadicCube 2)
    (F : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q)) (hFm : Measurable F)
    (hF : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∃ hω : MemBlockL2 (openCubeSet Q) (bandLoad M n terminal sigma e ω),
        F ω = toHilbertBlockL2OfBlockField hω) :
    ∃ C : Cutoff.CutoffSample 2 → Vec 2 → BlockVec 2,
      (∀ ω, ScalarVariation (openCubeSet Q) (C ω)) ∧
      AEStronglyMeasurable
        (cutoffTrialEnergy M terminal sigma Q (bandTrialField M n terminal sigma e C))
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      cutoffTrialEnergy M terminal sigma Q (bandTrialField M n terminal sigma e C) =ᵐ[
        (Cutoff.cutoffSampleLaw M).toMeasure] upperCellProjectedEnergy M terminal Q sigma hsigma F := by
  let C := fun ω => upperCellCorrectionField Q M.nu sigma M.nu_pos hsigma
    (oldCutoffSkewCoefficient terminal Q ω) (F ω)
  have hC (ω) : ScalarVariation (openCubeSet Q) (C ω) :=
    upper_cell_correction_variation Q M.nu sigma M.nu_pos hsigma
      (oldCutoffSkewCoefficient terminal Q ω) (F ω)
  have heq : cutoffTrialEnergy M terminal sigma Q (bandTrialField M n terminal sigma e C) =ᵐ[
      (Cutoff.cutoffSampleLaw M).toMeasure] upperCellProjectedEnergy M terminal Q sigma hsigma F := by
    filter_upwards [hF] with ω hω
    obtain ⟨hmem,hclass⟩ := hω
    change volumeAverage (openCubeSet Q) (fun x => responseFrameEnergyDensity M.nu sigma
      (Cutoff.cutoff terminal ω x 1 0) ((bandLoad M n terminal sigma e ω+C ω) x)) = _
    dsimp only [C,upperCellProjectedEnergy]
    rw [hclass]
    exact upper_cell_corrected_band_energy M n terminal sigma hsigma e Q ω hmem
  have hm := (upper_cell_projected_energy_measurable M terminal Q sigma hsigma F hFm).aestronglyMeasurable
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
  exact ⟨C,hC,hm.congr heq.symm,heq⟩

/-- Integrability and the integral transfer to the constructed actual trial.
This helper isolates the physical-carrier join, not a source energy bound. -/
theorem upper_cell_integrable_trial_from_load
    (M : ABKModel 2) (n terminal : ℤ) (sigma : ℝ) (hsigma : 0<sigma)
    (e : Vec 2) (Q : TriadicCube 2)
    (F : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q)) (hFm : Measurable F)
    (hF : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∃ hω : MemBlockL2 (openCubeSet Q) (bandLoad M n terminal sigma e ω),
        F ω = toHilbertBlockL2OfBlockField hω)
    (hi : Integrable (upperCellProjectedEnergy M terminal Q sigma hsigma F)
      (Cutoff.cutoffSampleLaw M).toMeasure) :
    ∃ C : Cutoff.CutoffSample 2 → Vec 2 → BlockVec 2,
      (∀ ω, ScalarVariation (openCubeSet Q) (C ω)) ∧
      Integrable (cutoffTrialEnergy M terminal sigma Q (bandTrialField M n terminal sigma e C))
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, cutoffTrialEnergy M terminal sigma Q (bandTrialField M n terminal sigma e C) ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ ω, upperCellProjectedEnergy M terminal Q sigma hsigma F ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  obtain ⟨C,hC,_,heq⟩ := upper_cell_trial_from_load M n terminal sigma hsigma e Q F hFm hF
  exact ⟨C,hC,hi.congr heq.symm,integral_congr_ae heq⟩

end
end ASDExplicitGamma.Scalar
