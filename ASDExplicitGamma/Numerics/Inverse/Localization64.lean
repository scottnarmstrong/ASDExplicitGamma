module

public import ASDExplicitGamma.Numerics.Inverse.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Generated data (exact rationals), checked by kernel reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse

def invLocalization64 : ℚ := 4*(320*64)^4*3^130/(∑ i ∈ Finset.range 513, (3^11/(6*64) : ℚ)^i/(Nat.factorial i))

theorem invLocalization64_payment :
    13^2*invLocalization64 < 9^2 := by
  decide +kernel

end ASDExplicitGamma.Numerics.Inverse
