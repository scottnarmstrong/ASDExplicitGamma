module

public import ASDExplicitGamma.Native.GenericSourceExtraPassNumerics

/-! Auxiliary invariant-region budgets for the refined child norm. These
constants only tighten intermediate comparisons; final source caps are unchanged. -/
@[expose] public section
namespace ASDExplicitGamma.Native

/-- The two finite refined-child comparison ranges. -/
def nativeSourceChildAuxHeight (high : Bool) : ℕ := if high then 160 else 40
/-- Outward physical variance coefficient on the chosen comparison range. -/
def nativeSourceChildAuxVariance (high : Bool) : ℚ := if high then 1739/1000000 else 789/500000
/-- Outward full128 trace on the chosen comparison range. -/
def nativeSourceChildAuxResponse (high : Bool) : ℚ := if high then 26000 else 18100
/-- Auxiliary norm barrier before multiplying by theta. -/
def nativeSourceChildAuxNorm (high : Bool) : ℚ := if high then 375 else 325
/-- Auxiliary root derivative payment before multiplying by theta. -/
def nativeSourceChildAuxCost (high : Bool) : ℚ := if high then 119 else 70
/-- Power-certified first Holder monomial at the barrier. -/
def nativeSourceChildAuxU1 (high : Bool) : ℚ := if high then 16443/20 else 3421/5
/-- Power-certified second Holder monomial at the barrier. -/
def nativeSourceChildAuxU2 (high : Bool) : ℚ := if high then 36049/20 else 72019/50

/-- All barrier radicals, p20 costs and strict margins are certified in
exact rational arithmetic, independently of the Gaussian estimates. -/
theorem native_source_child_aux_certificate (high : Bool) :
    let H := nativeSourceChildAuxHeight high
    let e := nativeSourceChildAuxVariance high
    let f := nativeSourceChildAuxResponse high
    let X := nativeSourceChildAuxNorm high
    let c := nativeSourceChildAuxCost high
    let u := nativeSourceChildAuxU1 high
    let v := nativeSourceChildAuxU2 high
    0 ≤ e ∧ 0 ≤ f ∧ 0 ≤ X ∧ 0 ≤ c ∧ 0 ≤ u ∧ 0 ≤ v ∧
    X^22*f^5 ≤ u^27 ∧ X^17*f^10 ≤ v^27 ∧
    e*((39*(H:ℚ)+38*(65399707/10^9:ℚ))*(2*(3683/2500:ℚ))+
      2*(65399707/10^9:ℚ)*(3683/2500:ℚ)*(4+u)+
      ((259713047/10^9:ℚ)+38*((259713047/10^9:ℚ)+(65399707/10^9:ℚ)))*
        (3683/2500:ℚ)^2*(4+v)) ≤ c ∧ (250:ℚ)+c<X := by
  cases high <;> decide +kernel

end ASDExplicitGamma.Native
