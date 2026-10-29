module
public import ASDExplicitGamma.Numerics.Native.PanelExp
public import ASDExplicitGamma.Numerics.Mirror.Composition
import Mathlib.Tactic.NormNum

/-! A shared-expression mirror for native setup and boundary-fixed panel formulas.
Every instruction consumes the earlier stack and pushes its result. Real evaluation ignores
all numerical enclosures; successful interval evaluation encloses that same real formula.
-/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics
open ASDExplicitGamma.Numerics.Mirror

def nativeZeroInterval : QInterval := ⟨0,0,le_rfl⟩

noncomputable def nativePlanReal : List ℝ → List Expr → List ℝ
  | stack, [] => stack
  | stack, e::es => nativePlanReal (evalReal (fun i => stack.getD i 0) e::stack) es

def nativePlanGrid : List QInterval → List Expr → Option (List QInterval)
  | stack, [] => some stack
  | stack, e::es =>
    match nativeInstructionGrid (fun i => stack.getD i nativeZeroInterval) e with
    | none => none
    | some out => nativePlanGrid (out::stack) es

/-- Every successful replay encloses the complete shared real expression graph. -/
theorem nativePlanGrid_sound
    (ops : List Expr) (stackI out : List QInterval) (stackR : List ℝ)
    (hin : ∀ i, QInterval.Contains (stackI.getD i nativeZeroInterval) (stackR.getD i 0))
    (h : nativePlanGrid stackI ops = some out) :
    ∀ i, QInterval.Contains (out.getD i nativeZeroInterval) ((nativePlanReal stackR ops).getD i 0) := by
  induction ops generalizing stackI stackR out with
  | nil =>
    simp only [nativePlanGrid, Option.some.injEq] at h
    subst out
    exact hin
  | cons e es ih =>
    cases he : nativeInstructionGrid (fun i => stackI.getD i nativeZeroInterval) e with
    | none => simp only [nativePlanGrid, he, reduceCtorEq] at h
    | some value =>
      have hv := nativeInstructionGrid_sound (fun i => stackI.getD i nativeZeroInterval)
        (fun i => stackR.getD i 0) hin e value he
      simp only [nativePlanGrid, he] at h
      have hs (i : ℕ) : QInterval.Contains ((value::stackI).getD i nativeZeroInterval)
          ((evalReal (fun i => stackR.getD i 0) e::stackR).getD i 0) := by
        cases i with
        | zero => exact hv
        | succ i => exact hin i
      exact ih (value::stackI) out (evalReal (fun i => stackR.getD i 0) e::stackR) hs h

def nativeSetupInputGrid (a0 xi0 : ℚ) : List QInterval :=
  [gridConstant 60 xi0,gridConstant 60 a0,nativeLogThreeInterval]

noncomputable def nativeSetupInputReal (a0 xi0 : ℚ) : List ℝ :=
  [(xi0 : ℝ),(a0 : ℝ),Real.log 3]

theorem nativeSetupInput_sound (a0 xi0 : ℚ) :
    ∀ i, QInterval.Contains ((nativeSetupInputGrid a0 xi0).getD i nativeZeroInterval)
      ((nativeSetupInputReal a0 xi0).getD i 0) := by
  intro i
  cases i with
  | zero => exact gridConstant_sound 60 xi0
  | succ i =>
    cases i with
    | zero => exact gridConstant_sound 60 a0
    | succ i =>
      cases i with
      | zero => exact nativeLogThreeInterval_sound
      | succ i =>
        change QInterval.Contains nativeZeroInterval (0 : ℝ)
        norm_num [QInterval.Contains,nativeZeroInterval]

def nativePlanUpperCheck (inputs : List QInterval) (ops : List Expr) (upper : ℚ) : Bool :=
  match nativePlanGrid inputs ops with
  | none => false
  | some out => decide ((out.getD 0 nativeZeroInterval).hi ≤ upper)

theorem nativePlanUpperCheck_sound (inputsI : List QInterval) (inputsR : List ℝ)
    (ops : List Expr) (upper : ℚ)
    (hin : ∀ i, QInterval.Contains (inputsI.getD i nativeZeroInterval) (inputsR.getD i 0))
    (hcheck : nativePlanUpperCheck inputsI ops upper = true) :
    (nativePlanReal inputsR ops).getD 0 0 ≤ (upper : ℝ) := by
  cases he : nativePlanGrid inputsI ops with
  | none => simp only [nativePlanUpperCheck,he,Bool.false_eq_true] at hcheck
  | some out =>
    have hn : (out.getD 0 nativeZeroInterval).hi ≤ upper := by
      apply of_decide_eq_true
      simpa only [nativePlanUpperCheck,he] using hcheck
    have hs := (nativePlanGrid_sound ops inputsI out inputsR hin he 0).2
    exact hs.trans ((Rat.cast_le (K := ℝ)).2 hn)

end ASDExplicitGamma.Numerics.Native
