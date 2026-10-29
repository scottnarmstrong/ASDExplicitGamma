module

public import ASDExplicitGamma.Numerics.Mirror.GridThree
public import ASDExplicitGamma.Numerics.Mirror.GridSqrt

/-!
# Compositional soundness for interval expressions

An expression is written once as a tree. Its real interpretation is independent of interval
evaluation; the grid evaluator either computes a sound enclosure or rejects a division,
square-root, or exponential whose domain is not certified by the current interval.
-/

@[expose] public section

namespace ASDExplicitGamma.Numerics.Mirror

open ASDExplicitGamma.Numerics

/-- Real arithmetic operations supported by the grid mirror. -/
inductive Expr where
  | const : ℚ → Expr
  | var : ℕ → Expr
  | neg : Expr → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | divPos : Expr → Expr → Expr
  | sqrt : Expr → Expr
  | exp : Expr → Expr
  deriving DecidableEq, Repr

/-- The readable real interpretation of an arithmetic expression. -/
noncomputable def evalReal (env : ℕ → ℝ) : Expr → ℝ
  | .const q => q
  | .var i => env i
  | .neg e => -evalReal env e
  | .add e₁ e₂ => evalReal env e₁ + evalReal env e₂
  | .sub e₁ e₂ => evalReal env e₁ - evalReal env e₂
  | .mul e₁ e₂ => evalReal env e₁ * evalReal env e₂
  | .divPos e₁ e₂ => evalReal env e₁ / evalReal env e₂
  | .sqrt e => Real.sqrt (evalReal env e)
  | .exp e => Real.exp (evalReal env e)

/-- Evaluate an expression over grid-rounded rational intervals. -/
def evalGrid (G n : ℕ) (hn : 5 ≤ n) (env : ℕ → QInterval) : Expr → Option QInterval
  | .const q => some (gridConstant G q)
  | .var i => some (env i)
  | .neg e => do
      let a ← evalGrid G n hn env e
      return neg G a
  | .add e₁ e₂ => do
      let a ← evalGrid G n hn env e₁
      let b ← evalGrid G n hn env e₂
      return add G a b
  | .sub e₁ e₂ => do
      let a ← evalGrid G n hn env e₁
      let b ← evalGrid G n hn env e₂
      return sub G a b
  | .mul e₁ e₂ => do
      let a ← evalGrid G n hn env e₁
      let b ← evalGrid G n hn env e₂
      return mul G a b
  | .divPos e₁ e₂ => do
      let a ← evalGrid G n hn env e₁
      let b ← evalGrid G n hn env e₂
      if h : 0 < b.lo then return divPos G a b h else none
  | .sqrt e => do
      let a ← evalGrid G n hn env e
      if h : 0 ≤ a.lo then return sqrt G a h else none
  | .exp e => do
      let a ← evalGrid G n hn env e
      if hlo : -50 ≤ a.lo then
        if hhi : a.hi ≤ 50 then return exp G n a hn hlo hhi else none
      else none

/-- Compositional soundness: every successful grid evaluation contains the corresponding
real expression value. -/
theorem evalGrid_sound (G n : ℕ) (hn : 5 ≤ n)
    (envI : ℕ → QInterval) (envR : ℕ → ℝ)
    (henv : ∀ i, QInterval.Contains (envI i) (envR i)) :
    ∀ e out, evalGrid G n hn envI e = some out →
      QInterval.Contains out (evalReal envR e) := by
  intro e
  induction e with
  | const q =>
      intro out h
      simp only [evalGrid, Option.some.injEq] at h
      subst out
      exact gridConstant_sound G q
  | var i =>
      intro out h
      simp only [evalGrid, Option.some.injEq] at h
      subst out
      simpa [evalReal] using henv i
  | neg e ih =>
      intro out h
      cases he : evalGrid G n hn envI e with
      | none => simp [evalGrid, he] at h
      | some a =>
          simp [evalGrid, he] at h
          subst out
          simpa [evalReal] using neg_sound G (ih a he)
  | add e₁ e₂ ih₁ ih₂ =>
      intro out h
      cases h₁ : evalGrid G n hn envI e₁ with
      | none => simp [evalGrid, h₁] at h
      | some a =>
        cases h₂ : evalGrid G n hn envI e₂ with
        | none => simp [evalGrid, h₁, h₂] at h
        | some b =>
          simp [evalGrid, h₁, h₂] at h
          subst out
          exact add_sound G (ih₁ a h₁) (ih₂ b h₂)
  | sub e₁ e₂ ih₁ ih₂ =>
      intro out h
      cases h₁ : evalGrid G n hn envI e₁ with
      | none => simp [evalGrid, h₁] at h
      | some a =>
        cases h₂ : evalGrid G n hn envI e₂ with
        | none => simp [evalGrid, h₁, h₂] at h
        | some b =>
          simp [evalGrid, h₁, h₂] at h
          subst out
          exact sub_sound G (ih₁ a h₁) (ih₂ b h₂)
  | mul e₁ e₂ ih₁ ih₂ =>
      intro out h
      cases h₁ : evalGrid G n hn envI e₁ with
      | none => simp [evalGrid, h₁] at h
      | some a =>
        cases h₂ : evalGrid G n hn envI e₂ with
        | none => simp [evalGrid, h₁, h₂] at h
        | some b =>
          simp [evalGrid, h₁, h₂] at h
          subst out
          exact mul_sound G (ih₁ a h₁) (ih₂ b h₂)
  | divPos e₁ e₂ ih₁ ih₂ =>
      intro out h
      cases h₁ : evalGrid G n hn envI e₁ with
      | none => simp [evalGrid, h₁] at h
      | some a =>
        cases h₂ : evalGrid G n hn envI e₂ with
        | none => simp [evalGrid, h₁, h₂] at h
        | some b =>
          by_cases hb : 0 < b.lo
          · simp [evalGrid, h₁, h₂, hb] at h
            subst out
            exact divPos_sound G (ih₁ a h₁) hb (ih₂ b h₂)
          · simp [evalGrid, h₁, h₂, hb] at h
  | sqrt e ih =>
      intro out h
      cases he : evalGrid G n hn envI e with
      | none => simp [evalGrid, he] at h
      | some a =>
          by_cases ha : 0 ≤ a.lo
          · simp [evalGrid, he, ha] at h
            subst out
            exact sqrt_sound G ha (ih a he)
          · simp [evalGrid, he, ha] at h
  | exp e ih =>
      intro out h
      cases he : evalGrid G n hn envI e with
      | none => simp [evalGrid, he] at h
      | some a =>
          by_cases hlo : -50 ≤ a.lo
          · by_cases hhi : a.hi ≤ 50
            · simp [evalGrid, he, hlo, hhi] at h
              subst out
              exact exp_sound G n hn hlo hhi (ih a he)
            · simp [evalGrid, he, hlo, hhi] at h
          · simp [evalGrid, he, hlo] at h

end ASDExplicitGamma.Numerics.Mirror
