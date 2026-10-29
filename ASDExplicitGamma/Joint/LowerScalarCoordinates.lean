module

public import ASDExplicitGamma.Statements.NativeInductionState

/-! The two target lower-scalar coordinates, projected from SC-LOWER-CORRIDOR. -/

@[expose] public section

namespace ASDExplicitGamma.Joint

open Algsuperdiff.Section3

/-- Project the lower corridor at target `N` from its strict-past producer. -/
theorem lower_scalar_n_of_corridor
    (M : ABKModel 2) (h : ℝ) (N : ℤ)
    (hcorridor : M.nu ≤ (Annealed.sigmaBar M N : ℝ) ∧
      (31 / 50) * shellVarianceSum h M.gamma N + (19 / 50) * M.nu ^ 2 ≤
        (Annealed.sigmaBar M N : ℝ) ^ 2) :
    M.nu ≤ (Annealed.sigmaBar M N : ℝ) ∧
      (31 / 50) * shellVarianceSum h M.gamma N + (19 / 50) * M.nu ^ 2 ≤
        (Annealed.sigmaBar M N : ℝ) ^ 2 :=
  hcorridor

end ASDExplicitGamma.Joint
