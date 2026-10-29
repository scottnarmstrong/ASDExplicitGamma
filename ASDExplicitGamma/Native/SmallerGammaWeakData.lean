module

public import ASDExplicitGamma.Native.GenericSourceChildRows

/-! Exact positive endpoint allocations for the completed source prefix.
The first seventeen depths use the minimum of two bounds for the same mean;
all later finite depths and both complete-tail allowances are retained. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.Native

/-- Positive endpoint mean allocation. Only depths zero through sixteen
receive a parent replacement; the remaining refined head is unchanged. -/
def nativeSourceCompletedHeadMean (d : Fin 56) : ℚ :=
  if d.val < 17 then
    min (nativeSourceChildRationalWitness d) (nativeBoundaryParentCaps.getD d.val 0)
  else nativeSourceChildRationalWitness d

/-- The full finite positive mean head, through gap 64, in the endpoint
upper geometric weights. The complete post-gap-64 tail is paid separately. -/
def nativeSourceCompletedWeightedHead (r : Fin 6) : ℚ :=
  ∑ j : Fin (56-r.val),
    ((759836/1000000:ℚ)^2*nativeE (2*nativeGamma))^j.val *
      nativeSourceCompletedHeadMean ⟨r.val+j.val, by omega⟩

/-- All parent entries that enter the source prefix are nonnegative. -/
theorem native_source_parent_caps_nonneg (d : Fin 17) :
    0 ≤ nativeBoundaryParentCaps.getD d.val 0 := by
  revert d
  decide +kernel

/-- Positivity of every retained finite mean allocation. -/
theorem native_source_completed_head_nonneg (d : Fin 56) :
    0 ≤ nativeSourceCompletedHeadMean d := by
  unfold nativeSourceCompletedHeadMean
  split_ifs with hd
  · exact le_min (native_source_child_rational_witness_nonneg d)
      (native_source_parent_caps_nonneg ⟨d.val, hd⟩)
  · exact native_source_child_rational_witness_nonneg d

/-- The positive head, the entire mean tail, and the entire rare-trace
companion lie below each exact completed weak endpoint. This is a closed
rational certificate, not a premise about the actual law. -/
theorem native_source_completed_weak_endpoint (r : Fin 6) :
    (1-(759835/1000000:ℚ)^2) *
      (nativeB * (nativeSourceCompletedWeightedHead r+1/100000) +
        nativeEps*10^12) ≤ nativeCompletedWeakRows.getD r.val 0 := by
  fin_cases r <;> decide +kernel

end ASDExplicitGamma.Native
