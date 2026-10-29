module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalMeanSplit

/-! The actual principal trial energy is the coarse response of the centered
terminal coefficient, evaluated at the gauged physical mean (e,w_U). -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Variational Inverse
noncomputable section

/-- The actual principal energy is exactly the centered terminal coarse
quadratic. The representation premise is supplied by the actual measurable load lift. -/
theorem upper_cell_physical_principal_gauge
    (M : ABKModel 2) (n terminal : ℤ) (sigma : ℝ) (hsigma : 0 < sigma)
    (e : Vec 2) (Q : TriadicCube 2)
    (F : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q))
    (hF : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∃ hω : MemBlockL2 (openCubeSet Q) (bandLoad M n terminal sigma e ω),
        F ω = toHilbertBlockL2OfBlockField hω) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let g := cubeAverage Q (laterScalarBand n terminal (fun _ => sigma⁻¹) ω)
      let k := oldCutoffSkewCoefficient terminal Q ω
      let centered := k - BoundedContinuousFunction.const (closure (openCubeSet Q)) (sigma*g)
      let B := (scalarFrameRealization Q M.nu sigma M.nu_pos hsigma k).energyBilin
      let S := scalarProjectionResidual Q M.nu sigma M.nu_pos hsigma k
        (upperCellResetMeanField Q (F ω))
      let P := (e,upperCellPhysicalPotentialMean M n terminal sigma⁻¹ e Q ω)
      B S S = blockVecDot P (blockMatVecMul
        (coarseBlockMatrix (openCubeSet Q) (responseFramePlanarCoefficientField M.nu sigma centered)) P) := by
  filter_upwards [upper_cell_canonical_gauged_mean M n terminal sigma e Q F hF] with ω hω
  let g := cubeAverage Q (laterScalarBand n terminal (fun _ => sigma⁻¹) ω)
  let k := oldCutoffSkewCoefficient terminal Q ω
  let centered := k-BoundedContinuousFunction.const (closure (openCubeSet Q)) (sigma*g)
  have hh := upper_cell_principal_constant_gauge Q M.nu sigma M.nu_pos hsigma
    centered g (upperCellResetMeanValue Q (F ω))
  dsimp only at hh ⊢
  have hadd : centered+BoundedContinuousFunction.const (closure (openCubeSet Q)) (sigma*g) = k :=
    sub_add_cancel _ _
  rw [hadd,hω] at hh
  rw [upper_cell_constant_projection_energy Q M.nu sigma M.nu_pos hsigma centered
    (e,upperCellPhysicalPotentialMean M n terminal sigma⁻¹ e Q ω)] at hh
  exact hh

end
end ASDExplicitGamma.Scalar
