module

public import ASDExplicitGamma.Native.HeatOldIterationSound
public import ASDExplicitGamma.Native.HeatOldEndpoint

/-! The raw initialization of the OLD producer majorizes the real source bill. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native
noncomputable section

/-- Every selected solve is in the physical finite-prefix domain. -/
theorem heat_configured_gap_bounds : ∀ j : Fin 153,
    1 ≤ (nativeConfiguredSystem j).gap ∧ (nativeConfiguredSystem j).gap ≤ 161 := by
  decide +kernel

/-- The exact raw moment increment is rounded outward before any OLD pass. -/
theorem heat_old_raw_increment_le (height : ℕ) :
    nativeSourceRawMomentIncrement height (nativeRaw height).2.1 (nativeRaw height).1 ≤
      ((nativeRaw height).2.2:ℝ) := by
  let f := (nativeRaw height).1
  let e := (nativeRaw height).2.1
  let r : ℚ := e*(((4*20-2)*height+4*19*(521/1000))*nativeB+
    2*(521/1000)*nativeB*f+((1975/1000)+2*19*(1565/1000))*nativeB^2*f)
  have hr : (r:ℝ) ≤ (nativeUp r:ℝ) := by exact_mod_cast nativeUp_ge r
  change _ ≤ (nativeUp r:ℝ)
  apply le_trans (le_of_eq ?_) hr
  dsimp [r,e,f,nativeSourceRawMomentIncrement,nativeSourceK,nativeSourceM,nativeSourceQ,nativeSourceB128,nativeB]
  push_cast
  ring

end
end ASDExplicitGamma.Native
