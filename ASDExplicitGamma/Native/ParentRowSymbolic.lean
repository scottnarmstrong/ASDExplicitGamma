module

public import ASDExplicitGamma.Native.ParentRowProgram

/-! Exact symbolic substitution for source-program coefficient identification.
Every reflected expression is checked by the kernel and interpreted over reals. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native Numerics.Mirror
noncomputable section

/-- Substitute source expressions for the stack variables of one instruction. -/
def parentRowSubst (env : ℕ → Expr) : Expr → Expr
  | .const q => .const q
  | .var i => env i
  | .neg e => .neg (parentRowSubst env e)
  | .add e f => .add (parentRowSubst env e) (parentRowSubst env f)
  | .sub e f => .sub (parentRowSubst env e) (parentRowSubst env f)
  | .mul e f => .mul (parentRowSubst env e) (parentRowSubst env f)
  | .divPos e f => .divPos (parentRowSubst env e) (parentRowSubst env f)
  | .sqrt e => .sqrt (parentRowSubst env e)
  | .exp e => .exp (parentRowSubst env e)

/-- Symbolic substitution commutes with the actual real interpretation. -/
theorem parent_row_subst_eval (env : ℕ → ℝ) (vars : ℕ → Expr) (e : Expr) :
    evalReal env (parentRowSubst vars e)=evalReal (fun i => evalReal env (vars i)) e := by
  induction e <;> simp_all only [parentRowSubst,evalReal]

/-- The same stack program run in exact expressions. -/
def parentRowExprPlan : List Expr → List Expr → List Expr
  | stack, [] => stack
  | stack, e::ops =>
      parentRowExprPlan (parentRowSubst (fun i => stack.getD i (.const 0)) e::stack) ops

/-- The symbolic stack denotes exactly the real stack, including defaults. -/
theorem parent_row_expr_plan_sound (env : ℕ → ℝ) (stack ops : List Expr) :
    nativePlanReal (stack.map (evalReal env)) ops =
      (parentRowExprPlan stack ops).map (evalReal env) := by
  induction ops generalizing stack with
  | nil => rfl
  | cons e ops ih =>
    simp only [nativePlanReal,parentRowExprPlan]
    rw [←ih,List.map_cons,parent_row_subst_eval]
    congr 2
    congr 1
    funext i
    simpa only [evalReal,Rat.cast_zero] using List.getD_map stack (.const 0) (n := i) (evalReal env)

/-- A symbolic prefix determines the corresponding final real entry. -/
theorem parent_row_symbolic_entry (env : ℕ → ℝ) (stack headOps tailOps : List Expr)
    (i : ℕ) :
    (nativePlanReal (stack.map (evalReal env)) (headOps++tailOps)).getD (tailOps.length+i) 0 =
      evalReal env ((parentRowExprPlan stack headOps).getD i (.const 0)) := by
  rw [nativePlanReal_append,old_signed_plan_real_tail,parent_row_expr_plan_sound]
  simpa only [evalReal,Rat.cast_zero] using List.getD_map (parentRowExprPlan stack headOps) (.const 0) (n := i) (evalReal env)

end
end ASDExplicitGamma.Native
