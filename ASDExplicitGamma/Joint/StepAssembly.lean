module

public import ASDExplicitGamma.Statements.NativeInductionState

/-! Assemble the eight fixed-target coordinates of the native induction state. -/

@[expose] public section

namespace ASDExplicitGamma.Joint

open Algsuperdiff.Section3
open scoped ENNReal

/-- Conjoin the seven fixed-target component outputs in the frozen state order. -/
theorem step_assembly_of_components
    (M : ABKModel 2) (h : ℝ) (N : ℤ)
    (hOrdinary : ordinaryMean M N ≤ ENNReal.ofReal (3 / 50 * theta M))
    (hStrong : strong20 M N ≤ ENNReal.ofReal (2379 / 2500 * theta M))
    (hRoot : root20 M N ≤ ENNReal.ofReal (2013 / 10000 * theta M))
    (hBufferHistory : buffer40History M N ≤ ENNReal.ofReal (61 / 10 * theta M))
    (hBufferMean : bufferMean M N ≤ ENNReal.ofReal (8 / 25 * theta M))
    (hLower : M.nu ≤ (Annealed.sigmaBar M N : ℝ) ∧
      (31 / 50) * shellVarianceSum h M.gamma N + (19 / 50) * M.nu ^ 2 ≤
        (Annealed.sigmaBar M N : ℝ) ^ 2)
    (hUpper : (Annealed.sigmaBar M N : ℝ) ^ 2 ≤
      M.nu ^ 2 + (13 / 8 : ℝ) * shellVarianceSum h M.gamma N) :
    nativeInductionState M h N := by
  exact ⟨hOrdinary, hStrong, hRoot, hBufferHistory, hBufferMean,
    hLower.1, hLower.2, hUpper⟩

end ASDExplicitGamma.Joint
