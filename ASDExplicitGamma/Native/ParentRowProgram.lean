module

public import ASDExplicitGamma.Native.OldSignedQ1VarianceClock

/-! Source-program identities extracted without expanding unrelated nodes. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- The first constant remains available at its exact final stack index. -/
theorem parent_row_program_first_constant
    (inputs : List ℝ) (q : ℚ) (ops : List Expr) :
    (nativePlanReal inputs (.const q::ops)).getD ops.length 0 = (q:ℝ) := by
  change (nativePlanReal ((q:ℝ)::inputs) ops).getD (ops.length+0) 0 = _
  rw [old_signed_plan_real_tail]
  rfl

/-- A multiplication instruction relates three entries of the same final
source stack. Later instructions preserve all three entries. -/
theorem parent_row_program_mul (inputs : List ℝ) (headOps tailOps : List Expr)
    (p q : ℕ) :
    let values := nativePlanReal inputs (headOps++(.mul (.var p) (.var q)::tailOps))
    values.getD tailOps.length 0 =
      values.getD (tailOps.length+(p+1)) 0*values.getD (tailOps.length+(q+1)) 0 := by
  dsimp only
  rw [nativePlanReal_append]
  simp only [nativePlanReal]
  conv_lhs => rw [show tailOps.length=tailOps.length+0 from (Nat.add_zero _).symm]
  rw [old_signed_plan_real_tail,old_signed_plan_real_tail,old_signed_plan_real_tail]
  rfl

end
end ASDExplicitGamma.Native
