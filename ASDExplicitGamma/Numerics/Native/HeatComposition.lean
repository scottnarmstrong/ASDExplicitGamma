module
public import ASDExplicitGamma.Numerics.Native.Heat

/-! Composition of the configured 48-pass native heat recursion. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

theorem nativeHeatPasses_add (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (coef fixed : List ℚ) (base : ℚ) (n m : ℕ) (y : ℚ) :
    nativeHeatPasses old frames coef fixed base (n+m) y =
      nativeHeatPasses old frames coef fixed base m (nativeHeatPasses old frames coef fixed base n y) := by
  induction n generalizing y with
  | zero => simp only [Nat.zero_add,nativeHeatPasses]
  | succ n ih => simp only [Nat.succ_add,nativeHeatPasses,ih]

end ASDExplicitGamma.Numerics.Native
