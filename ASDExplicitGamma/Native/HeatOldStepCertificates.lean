module

public import ASDExplicitGamma.Native.HeatIndividualOldCertificates
public import ASDExplicitGamma.Native.GenericSourceExtraPassNumerics

/-! Arithmetic certificates for the four OLD refinements preceding each solve. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

/-- The literal sequence of OLD moment increments. -/
def heatOldIncrement (height : ℕ) (f e hc : ℚ) : ℕ → ℚ
  | 0 => hc
  | n+1 => nativeOldStep height f e (heatOldIncrement height f e hc n)

/-- Soundness data for the three radical expressions consumed by one OLD
refinement. The certificates use integer powers, not real-root assumptions. -/
def HeatOldStepValid (f hc : ℚ) : Prop :=
  let x := (7/2)*nativeA+hc
  let u := x*nativeRootUp ((f/x)^5) 27
  let v := x*nativeRootUp ((f/x)^10) 27
  let d := nativeRootUp (2*x) 2
  0 ≤ hc ∧ 0 < x ∧ 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ d ∧
    x^22*f^5 ≤ u^27 ∧ x^17*f^10 ≤ v^27 ∧ 2*x ≤ d^2

/-- The source's four nested updates are precisely this finite iteration. -/
theorem heat_old_from_four (height : ℕ) (f e hc : ℚ) :
    (nativeOldFrom height f e hc).x =
      nativeUp ((7/2)*nativeA+heatOldIncrement height f e hc 4) := rfl

end ASDExplicitGamma.Native
