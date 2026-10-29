module

public import ASDExplicitGamma.Numerics.Inverse.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Generated data (exact rationals), checked by kernel reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse

def invLocalization128 : ℚ := 4*(320*128)^4*3^130/(∑ i ∈ Finset.range 513, (3^11/(6*128) : ℚ)^i/(Nat.factorial i))

theorem invLocalization128_payment :
    13^2*invLocalization128 < 9^2 := by
  decide +kernel

end ASDExplicitGamma.Numerics.Inverse
