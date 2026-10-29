module

public import ASDExplicitGamma.Scalar.UpperCellEnergyCorrection

/-! The physical cell energy of the constructed trial is exactly the
weighted Hilbert energy of the full terminal-coefficient projection. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- The actual cutoff Hilbert energy is the literal physical density average
in any fixed positive scalar frame. -/
theorem upper_cell_cutoff_hilbert_energy
    (M : ABKModel 2) (N : ℤ) (sigma : ℝ) (hsigma : 0 < sigma)
    (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) (X : HilbertBlockL2 (openCubeSet Q)) :
    (scalarFrameRealization Q M.nu sigma M.nu_pos hsigma
      (oldCutoffSkewCoefficient N Q ω)).energyBilin X X =
    volumeAverage (openCubeSet Q) (fun x => responseFrameEnergyDensity M.nu sigma
      (Cutoff.cutoff N ω x 1 0) (hilbertBlockL2ToBlockL2 X x)) := by
  let finiteCell : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hh := responseFrameMu_energy_eq_volumeAverage_density
    (measurableSet_openCubeSet Q)
    (show 0 < (volume (openCubeSet Q)).toReal by
      rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
    M.nu sigma M.nu_pos hsigma (oldCutoffSkewCoefficient N Q ω) X
  change (scalarFrameRealization Q M.nu sigma M.nu_pos hsigma
    (oldCutoffSkewCoefficient N Q ω)).energyBilin X X = _ at hh
  rw [hh]
  unfold volumeAverage
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  rw [old_cutoff_skew_coefficient_value N Q ω hx]

/-- For the full band load, the constructed physical trial has precisely the
projected energy. This identifies the integral carrier. -/
theorem upper_cell_corrected_band_energy
    (M : ABKModel 2) (n N : ℤ) (sigma : ℝ) (hsigma : 0 < sigma)
    (e : Vec 2) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2)
    (hF : MemBlockL2 (openCubeSet Q) (bandLoad M n N sigma e ω)) :
    let X := toHilbertBlockL2OfBlockField hF
    let k := oldCutoffSkewCoefficient N Q ω
    let C := upperCellCorrectionField Q M.nu sigma M.nu_pos hsigma k X
    let Z := scalarProjectionResidual Q M.nu sigma M.nu_pos hsigma k X
    volumeAverage (openCubeSet Q) (fun x => responseFrameEnergyDensity M.nu sigma
      (Cutoff.cutoff N ω x 1 0) ((bandLoad M n N sigma e ω+C) x)) =
      (scalarFrameRealization Q M.nu sigma M.nu_pos hsigma k).energyBilin Z Z := by
  dsimp only
  rw [upper_cell_cutoff_hilbert_energy M N sigma hsigma Q ω]
  have hEq := upper_cell_corrected_field_eq Q M.nu sigma M.nu_pos hsigma
    (oldCutoffSkewCoefficient N Q ω) hF
  unfold volumeAverage
  congr 1
  apply integral_congr_ae
  filter_upwards [hEq] with x hx
  rw [hx]

end
end ASDExplicitGamma.Scalar
