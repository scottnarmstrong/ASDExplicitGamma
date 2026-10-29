module
public import ASDExplicitGamma.Numerics.Native.State
import Mathlib.Tactic.NormNum

/-! Composition of bounded native Taylor runs; the chunk boundaries are numeric certificates. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeTaylorSteps_add (s : NativeScaledSystem) (a b n : ℕ) (term accum : List ℚ) :
    nativeTaylorSteps s (a+b) n term accum =
      let out := nativeTaylorSteps s a n term accum
      nativeTaylorSteps s b (n+a) out.1 out.2 := by
  induction a generalizing n term accum with
  | zero => simp only [Nat.zero_add, nativeTaylorSteps, Nat.add_zero]
  | succ a ih =>
    simp only [Nat.succ_add, nativeTaylorSteps]
    rw [ih]
    simp only [Nat.add_comm, Nat.add_left_comm]

end ASDExplicitGamma.Numerics.Native
