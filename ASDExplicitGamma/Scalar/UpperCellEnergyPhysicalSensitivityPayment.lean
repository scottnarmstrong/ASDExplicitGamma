module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalLoadMoment
public import ASDExplicitGamma.Scalar.UpperCellEnergySensitivityPayment

/-! The actual physical sensitivity payment, with all analytic inputs discharged. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- The source block has positive integer height on the full gamma range. -/
theorem upper_cell_source_height_pos (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) :
    0 < ⌊(17/50:ℝ)/M.gamma⌋.toNat := by
  have hh : 1 ≤ (17/50:ℝ)/M.gamma := (le_div_iff₀ M.shellPrefix.gamma_pos).mpr (by
    change M.gamma ≤ 17/50000 at hg
    linarith only [hg])
  have hp := Int.floor_pos.mpr hh
  omega

/-- The literal all-event sensitivity integrand is integrable and paid by
exactly the certified source sensitivity expression. No estimate, moment,
independence, or future-state hypothesis remains. -/
theorem upper_cell_physical_sensitivity_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (n : ℤ) (hn : n < N)
    {e : Vec 2} (he : Book.Ch02.vecNorm e = 1) :
    let height := ⌊(17/50:ℝ)/M.gamma⌋.toNat
    let Q := originCube 2 (n-14)
    let A := fun ω => 1+2*(lagTraceHistory M n 14 ω).toReal+
      Real.sqrt (2*(lagTraceHistory M n 14 ω).toReal)
    let F := upperCellPhysicalEnvelope M n height (cubeCenter Q)
    let P := upperCellPhysicalLoadMagnitude M n (n+height) (Annealed.sigmaBar M n:ℝ)⁻¹ e Q
    let E := fun ω => 6*A ω^2*F ω*(1+2*F ω+4*F ω^2)*P ω^2
    Integrable E (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, E ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ upperCellSensitivityProfile M.gamma := by
  let height := ⌊(17/50:ℝ)/M.gamma⌋.toNat
  let Q := originCube 2 (n-14)
  have hA := upper_cell_old_matrix_majorant_L2 M h hM hg N hpast n hn
  have hF := upper_cell_physical_envelope_L6 M h hM n height
    (upper_cell_source_height_pos M hg) (cubeCenter Q) hg (hpast n hn)
  have hP := upper_cell_physical_load_magnitude_L4 M h hM n hg (hpast n hn) he Q
  apply upper_cell_sensitivity_payment (Cutoff.cutoffSampleLaw M).toMeasure _ _ _
    hA.1 hF.1.aestronglyMeasurable hP.1.aestronglyMeasurable
  · intro ω
    positivity
  · intro ω
    exact upper_cell_band_envelope_nonneg _ _ _ _ _ _ (by positivity) (sq_nonneg _) ω
  · exact upper_cell_physical_load_magnitude_nonneg M n (n+height) _ e Q
  · positivity
  · unfold upperCellFProfile
    positivity
  · exact hA.2
  · exact upper_cell_physical_envelope_eLpNorm_le M h hM n height
      (upper_cell_source_height_pos M hg) (cubeCenter Q) hg (hpast n hn)
  · exact hP.2
  · exact upper_cell_physical_majorant_pair_independent M n 14 height _ e Q

end
end ASDExplicitGamma.Scalar
