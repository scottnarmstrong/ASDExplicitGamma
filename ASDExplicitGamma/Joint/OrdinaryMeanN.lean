module

public import ASDExplicitGamma.Statements.NativeInductionState
/-! The target ordinary mean, projected from the exact Part D producer output. -/

@[expose] public section

namespace ASDExplicitGamma.Joint

open Algsuperdiff.Section3
open scoped ENNReal

/-- Project the exact target ordinary-mean conclusion of
MA-ORDINARY-RETURN. -/
theorem ordinary_mean_n_of_main_return
    (M : ABKModel 2) (N : ℤ)
    (hreturn : ordinaryMean M N ≤ ENNReal.ofReal (3 / 50 * theta M)) :
    ordinaryMean M N ≤ ENNReal.ofReal (3 / 50 * theta M) :=
  hreturn

end ASDExplicitGamma.Joint
