module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandLoad
public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalEnergy

/-! An actual random cell trial and its measurable energy. Its integrability
and numerical energy bound are the remaining stochastic moment obligations. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- The scalar energy of a measurable random Hilbert field is measurable
under the actual terminal cutoff coefficient. -/
theorem upper_cell_random_energy_measurable
    (M : ABKModel 2) (N : ℤ) (sigma : ℝ) (hsigma : 0 < sigma)
    (Q : TriadicCube 2) (Z : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q))
    (hZ : Measurable Z) :
    Measurable (fun ω => (scalarFrameRealization Q M.nu sigma M.nu_pos hsigma
      (oldCutoffSkewCoefficient N Q ω)).energyBilin (Z ω) (Z ω)) := by
  let finiteCell : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let : IsSeparable (volumeMeasureOn (openCubeSet Q)) := inferInstance
  let : Fact (1 ≤ (2:ENNReal)) := ⟨by norm_num⟩
  let : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
  let : SecondCountableTopology (HilbertBlockL2 (openCubeSet Q)) := inferInstance
  have hB := measurable_oldCutoff_scalarFrameEnergyBilin N Q M.nu sigma M.nu_pos hsigma
  exact (hB.clm_apply hZ).clm_apply hZ

end
end ASDExplicitGamma.Scalar
