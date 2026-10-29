module
public import ASDExplicitGamma.Numerics.Native.TailBounds

/-! The literal unrounded raw-frame tail formula is bounded by the outward replay. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeSourceRawFrame (h : ℕ) : ℚ :=
  nativeE (2*nativeGamma*h)*
    ((1+1/1000)*(nativeAvg*nativeA+(nativeRaw h).2.2)+
      8*(1+1000)*((11/10)*nativeGamma*h)^2)

def nativeSourceHistoryTail (offset : ℕ) : ℚ :=
  nativeC0*nativeSourceRawFrame offset*1287^4*(9/10)^1286*(Nat.factorial 4)*10^5

theorem nativeSourceStrongTail_le : nativeSourceHistoryTail 9 ≤ nativeStrongTail := by
  decide +kernel

theorem nativeSourceBufferTail_le : nativeSourceHistoryTail 49 ≤ nativeBufferTail := by
  decide +kernel

end ASDExplicitGamma.Numerics.Native
