module

public import ASDExplicitGamma.Native.HeatRemainderControl

/-! Order bookkeeping for the finite bracket-dependent heat redistributions. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

/-- A finite heat pass preserves the previously proved cap as an alternative. -/
theorem native_heat_pass_le (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (coef fixed : List ℚ) (base y : ℚ) : nativeHeatPass old frames coef fixed base y ≤ y :=
  min_le_left _ _

/-- The exact source recursion tightens its starting cap after every finite
number of passes, in particular48; this makes no fixed-point assertion. -/
theorem native_heat_passes_le (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (coef fixed : List ℚ) (base : ℚ) (n : ℕ) (y : ℚ) :
    nativeHeatPasses old frames coef fixed base n y ≤ y := by
  induction n generalizing y with
  | zero => exact le_rfl
  | succ n ih =>
    exact (ih (nativeHeatPass old frames coef fixed base y)).trans
      (native_heat_pass_le old frames coef fixed base y)

end ASDExplicitGamma.Native
