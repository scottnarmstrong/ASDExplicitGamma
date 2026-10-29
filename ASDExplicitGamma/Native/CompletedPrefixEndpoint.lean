module

public import ASDExplicitGamma.Native.CompletedPrefixData
public import Mathlib.Data.Rat.BigOperators

/-! Connect the positive prefix identity to the exact six published endpoint
rows. Complete tails remain in the explicit nonnegative residual. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.Native
noncomputable section

/-- The exact source computation with corrected parent entries. -/
def nativeCompletedPrefixEndpointResult (r : Fin 6) : ℚ × ℚ :=
  nativeSourcePrefix r.val (nativeCompletedPrefixOldMean r) (nativeCompletedPrefixOldXi r)
    (nativeCompletedPrefixProfile r) nativeCompletedPrefixParents

/-- The source computation is exactly the published six-row data, including
its source r=0 mean, not a second approximation of that data. -/
theorem native_completed_prefix_endpoint_result (r : Fin 6) :
    nativeCompletedPrefixEndpointResult r =
      (nativeCompletedMeanRows.getD r.val 0,nativeCompletedWeakRows.getD r.val 0) := by
  revert r
  decide +kernel

end
end ASDExplicitGamma.Native
