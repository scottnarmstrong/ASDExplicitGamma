module

public import ASDExplicitGamma.Scalar.TwoLimits

/-! The scalar long-block conversion with the exact trial-energy conclusion
as its input. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

/-- The exact cell-energy integral bound converts to the long-block scalar
frame ratio through the no-loss theorem. The energy estimate remains the
single producer conclusion supplied by SC-UPPER-CELL-ENERGY. -/
theorem scalar_longblock_trial_of_cell_energy_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (n N : ℤ) (hnN : n < N)
    (hν : 0 < M.nu) (z ε : ℝ) (e : Vec 2) (he : vecDot e e = 1)
    (C : CutoffSample 2 → Vec 2 → BlockVec 2)
    (hC : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ScalarVariation (openCubeSet (originCube 2 (n-14))) (C ω))
    (hE : Integrable
      (cutoffTrialEnergy M N (Annealed.sigmaBar M n : ℝ)
        (originCube 2 (n-14))
        (bandTrialField M n N (Annealed.sigmaBar M n : ℝ) e C))
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (hTrialBound :
      (∫ ω, cutoffTrialEnergy M N (Annealed.sigmaBar M n : ℝ)
        (originCube 2 (n-14))
        (bandTrialField M n N (Annealed.sigmaBar M n : ℝ) e C) ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ 1 + z + ε) :
    (Annealed.sigmaBar M N : ℝ) ≤
      (Annealed.sigmaBar M n : ℝ) * (1 + z + ε) := by
  have hratio := no_loss_long_block M h hM hγ n N hnN hν
    (1 + z + ε) e he C hC hE hTrialBound
  simpa [mul_comm] using
    (div_le_iff₀ (Annealed.sigmaBar M n).property).1 hratio

end ASDExplicitGamma.Scalar
