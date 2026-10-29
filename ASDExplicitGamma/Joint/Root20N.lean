module

public import ASDExplicitGamma.Statements.NativeInductionState

/-! The singleton-root coordinate at one fixed target, projected from NA-STEP. -/

@[expose] public section

namespace ASDExplicitGamma.Joint

open Algsuperdiff.Section3
open scoped ENNReal

/-- Project the root-20 component of the target-`N` native step. -/
theorem root20_n_of_native_step
    (M : ABKModel 2) (N : ℤ)
    (hstep : strong20 M N ≤ ENNReal.ofReal (2379 / 2500 * theta M) ∧
      root20 M N ≤ ENNReal.ofReal (2013 / 10000 * theta M) ∧
      buffer40History M N ≤ ENNReal.ofReal (61 / 10 * theta M) ∧
      bufferMean M N ≤ ENNReal.ofReal (8 / 25 * theta M)) :
    root20 M N ≤ ENNReal.ofReal (2013 / 10000 * theta M) :=
  hstep.2.1

end ASDExplicitGamma.Joint
