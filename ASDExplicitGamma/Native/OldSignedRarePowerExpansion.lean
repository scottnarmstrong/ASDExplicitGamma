module

public import ASDExplicitGamma.Native.OldSignedRareTraceIntegral
public import ASDExplicitGamma.Inverse.RawRareExpansion
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Integrating the pointwise binomial rare-factor expansion before its moment bounds are applied. -/
@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Inverse
open scoped BigOperators

/-- Exact binomial expansion through the fourth source-bank power. -/
theorem old_signed_rare_power_binomial (beta R X : ℝ) (k : ℕ) (hk : k ≤ 4) :
    (beta+R)^k*X=beta^k*X+rareExpansionTail beta R X k := by
  unfold rareExpansionTail
  interval_cases k <;> norm_num [Finset.sum_Icc_succ_top,Nat.choose] <;> ring

end ASDExplicitGamma.Native
