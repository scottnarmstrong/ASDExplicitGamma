module

public import ASDExplicitGamma.Scalar.MolecularUpperBound
public import ASDExplicitGamma.Scalar.MolecularAlgebra

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Model

/-- SC-MOLECULAR-FIVE-FOUR for the genuine running diffusivity. -/
theorem sigmaBar_sq_le_molecular_five_four
    (M : ABKModel 2) (h : ℝ) (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) (m : ℤ)
    (hsmall : shellVarianceSum h M.gamma m ≤ M.nu ^ 2) :
    (Annealed.sigmaBar M m : ℝ) ^ 2 ≤ M.nu ^ 2 + 5 * shellVarianceSum h M.gamma m / 4 := by
  have hhalf : 0 ≤ ∫ ω, cutoffProjectedEnergy M planarBasis0 m m ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
    integral_nonneg (fun ω => cutoffProjectedEnergy_nonneg M planarBasis0 m m ω)
  rw [integral_cutoffProjectedEnergy M h hM planarBasis0_unit m m] at hhalf
  have hB : 0 ≤ shellVarianceSum h M.gamma m := by linarith only [hhalf]
  exact molecular_five_four_of_upper M.nu_pos hB hsmall
    (M.nu_pos.le.trans (nu_le_sigmaBar M m)) (sigmaBar_le_molecular_upper M h hM m)

end ASDExplicitGamma.Scalar
