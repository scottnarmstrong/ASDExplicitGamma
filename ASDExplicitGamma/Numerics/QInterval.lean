module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# Rational intervals and expression evaluation

All certificate arithmetic is over `ℚ`. The real interpretation is used only in
soundness theorems; executable definitions reduce to rational arithmetic.
-/

@[expose] public section

namespace ASDExplicitGamma.Numerics

/-- A closed interval with rational endpoints in increasing order. -/
structure QInterval where
  lo : ℚ
  hi : ℚ
  valid : lo ≤ hi
  deriving DecidableEq, Repr

namespace QInterval

/-- The represented real numbers. -/
def Contains (i : QInterval) (x : ℝ) : Prop := (i.lo : ℝ) ≤ x ∧ x ≤ i.hi

/-- A point interval. -/
def point (q : ℚ) : QInterval := ⟨q, q, le_rfl⟩

/-- The largest absolute endpoint, used for a safe general product. -/
def radius (i : QInterval) : ℚ := max |i.lo| |i.hi|

theorem radius_nonneg (i : QInterval) : 0 ≤ radius i :=
  le_trans (abs_nonneg _) (le_max_left _ _)

theorem abs_le_radius {i : QInterval} {x : ℝ} (hx : Contains i x) :
    |x| ≤ (radius i : ℝ) := by
  change (i.lo : ℝ) ≤ x ∧ x ≤ i.hi at hx
  rcases le_total 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0]
    have hi0 : (0 : ℝ) ≤ i.hi := hx0.trans hx.2
    have hi0q : 0 ≤ i.hi := by exact_mod_cast hi0
    calc x ≤ i.hi := hx.2
      _ ≤ (radius i : ℝ) := by
        dsimp [radius]
        rw [abs_of_nonneg hi0q]
        exact_mod_cast (le_max_right |i.lo| i.hi)
  · rw [abs_of_nonpos hx0]
    have lo0 : (i.lo : ℝ) ≤ 0 := hx.1.trans hx0
    have lo0q : i.lo ≤ 0 := by exact_mod_cast lo0
    calc -x ≤ -i.lo := neg_le_neg hx.1
      _ ≤ (radius i : ℝ) := by
        dsimp [radius]
        rw [abs_of_nonpos lo0q]
        exact_mod_cast (le_max_left (-i.lo) |i.hi|)

/-- Sound addition of intervals. -/
def add (a b : QInterval) : QInterval :=
  ⟨a.lo + b.lo, a.hi + b.hi, add_le_add a.valid b.valid⟩

theorem add_sound {a b : QInterval} {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (add a b) (x + y) := by
  change (a.lo : ℝ) ≤ x ∧ x ≤ a.hi at hx
  change (b.lo : ℝ) ≤ y ∧ y ≤ b.hi at hy
  change ((a.lo + b.lo : ℚ) : ℝ) ≤ x + y ∧ x + y ≤ ((a.hi + b.hi : ℚ) : ℝ)
  exact ⟨by exact_mod_cast (add_le_add hx.1 hy.1),
    by exact_mod_cast (add_le_add hx.2 hy.2)⟩

/-- Sound multiplication, sharp when both intervals are nonnegative. -/
def mul (a b : QInterval) : QInterval :=
  if ha : 0 ≤ a.lo then
    if hb : 0 ≤ b.lo then
      ⟨a.lo * b.lo, a.hi * b.hi,
        mul_le_mul a.valid b.valid hb (ha.trans a.valid)⟩
    else
      ⟨-(radius a * radius b), radius a * radius b, by
        exact neg_le_self (mul_nonneg (radius_nonneg a) (radius_nonneg b))⟩
  else
    ⟨-(radius a * radius b), radius a * radius b, by
      exact neg_le_self (mul_nonneg (radius_nonneg a) (radius_nonneg b))⟩

theorem mul_sound {a b : QInterval} {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (mul a b) (x * y) := by
  change (a.lo : ℝ) ≤ x ∧ x ≤ a.hi at hx
  change (b.lo : ℝ) ≤ y ∧ y ≤ b.hi at hy
  unfold mul
  split_ifs with ha hb
  · change ((a.lo * b.lo : ℚ) : ℝ) ≤ x * y ∧ x * y ≤ ((a.hi * b.hi : ℚ) : ℝ)
    have haR : (0 : ℝ) ≤ a.lo := by exact_mod_cast ha
    have hbR : (0 : ℝ) ≤ b.lo := by exact_mod_cast hb
    have haValidR : (a.lo : ℝ) ≤ a.hi := by exact_mod_cast a.valid
    constructor
    · exact_mod_cast (mul_le_mul hx.1 hy.1 hbR (haR.trans hx.1))
    · exact_mod_cast (mul_le_mul hx.2 hy.2 (hbR.trans hy.1) (haR.trans haValidR))
  · have hxa := abs_le_radius hx
    have hyb := abs_le_radius hy
    have hrA : (0 : ℝ) ≤ (radius a : ℝ) := by exact_mod_cast radius_nonneg a
    have hprod : |x * y| ≤ (radius a : ℝ) * radius b := by
      rw [abs_mul]
      exact mul_le_mul hxa hyb (abs_nonneg _) hrA
    have hs := abs_le.mp hprod
    simp only [Contains]
    change ((-(radius a * radius b) : ℚ) : ℝ) ≤ x * y ∧
      x * y ≤ ((radius a * radius b : ℚ) : ℝ)
    exact_mod_cast hs
  · have hxa := abs_le_radius hx
    have hyb := abs_le_radius hy
    have hrA : (0 : ℝ) ≤ (radius a : ℝ) := by exact_mod_cast radius_nonneg a
    have hprod : |x * y| ≤ (radius a : ℝ) * radius b := by
      rw [abs_mul]
      exact mul_le_mul hxa hyb (abs_nonneg _) hrA
    have hs := abs_le.mp hprod
    simp only [Contains]
    change ((-(radius a * radius b) : ℚ) : ℝ) ≤ x * y ∧
      x * y ≤ ((radius a * radius b : ℚ) : ℝ)
    exact_mod_cast hs

/-- Reciprocal interval for a strictly positive interval. -/
def invPos (b : QInterval) (hb : 0 < b.lo) : QInterval :=
  ⟨b.hi⁻¹, b.lo⁻¹, (inv_le_inv₀ (by exact_mod_cast (lt_of_lt_of_le hb b.valid))
    (by exact_mod_cast hb)).2 b.valid⟩

theorem invPos_sound {b : QInterval} {y : ℝ} (hb : 0 < b.lo) (hy : Contains b y) :
    Contains (invPos b hb) y⁻¹ := by
  change (b.lo : ℝ) ≤ y ∧ y ≤ b.hi at hy
  have hbl : (0 : ℝ) < b.lo := by exact_mod_cast hb
  have hy0 : 0 < y := lt_of_lt_of_le hbl hy.1
  change ((b.hi⁻¹ : ℚ) : ℝ) ≤ y⁻¹ ∧ y⁻¹ ≤ ((b.lo⁻¹ : ℚ) : ℝ)
  constructor
  · simpa [one_div] using one_div_le_one_div_of_le hy0 hy.2
  · simpa [one_div] using one_div_le_one_div_of_le hbl hy.1

/-- Division by an interval with a positive lower endpoint. -/
def divPos (a b : QInterval) (hb : 0 < b.lo) : QInterval := mul a (invPos b hb)

theorem divPos_sound {a b : QInterval} {x y : ℝ} (ha : Contains a x) (hb : 0 < b.lo)
    (hy : Contains b y) : Contains (divPos a b hb) (x / y) := by
  simpa [divPos, div_eq_mul_inv] using mul_sound ha (invPos_sound hb hy)

end QInterval

/-- Rational arithmetic expression trees with named interval inputs. -/
inductive QExpr where
  | const : ℚ → QExpr
  | var : ℕ → QExpr
  | add : QExpr → QExpr → QExpr
  | mul : QExpr → QExpr → QExpr
  | div : QExpr → QExpr → QExpr
  deriving DecidableEq, Repr

/-- Evaluate an expression over rational intervals. Division is accepted only when its
  denominator interval is strictly positive. -/
def evalQExpr (env : ℕ → QInterval) : QExpr → Option QInterval
  | .const q => some (QInterval.point q)
  | .var i => some (env i)
  | .add a b =>
      match evalQExpr env a, evalQExpr env b with
      | some x, some y => some (QInterval.add x y)
      | _, _ => none
  | .mul a b =>
      match evalQExpr env a, evalQExpr env b with
      | some x, some y => some (QInterval.mul x y)
      | _, _ => none
  | .div a b =>
      match evalQExpr env a, evalQExpr env b with
      | some x, some y => if h : 0 < y.lo then some (QInterval.divPos x y h) else none
      | _, _ => none

/-- The real expression represented by a tree. -/
noncomputable def evalQExprReal (env : ℕ → ℝ) : QExpr → ℝ
  | .const q => q
  | .var i => env i
  | .add a b => evalQExprReal env a + evalQExprReal env b
  | .mul a b => evalQExprReal env a * evalQExprReal env b
  | .div a b => evalQExprReal env a / evalQExprReal env b

theorem evalQExpr_sound (envI : ℕ → QInterval) (envR : ℕ → ℝ)
    (henv : ∀ i, QInterval.Contains (envI i) (envR i)) :
    ∀ e out, evalQExpr envI e = some out → QInterval.Contains out (evalQExprReal envR e) := by
  intro e
  induction e with
  | const q =>
      intro out h
      simp [evalQExpr, evalQExprReal, QInterval.Contains, QInterval.point] at h ⊢
      subst out
      exact ⟨le_rfl, le_rfl⟩
  | var i =>
      intro out h
      simp only [evalQExpr, Option.some.injEq] at h
      subst out
      simpa [evalQExprReal] using henv i
  | add a b iha ihb =>
      intro out h
      cases h1 : evalQExpr envI a with
      | none => simp [evalQExpr, h1] at h
      | some x =>
        cases h2 : evalQExpr envI b with
        | none => simp [evalQExpr, h1, h2] at h
        | some y =>
          simp [evalQExpr, h1, h2] at h
          subst out
          exact QInterval.add_sound (iha x h1) (ihb y h2)
  | mul a b iha ihb =>
      intro out h
      cases h1 : evalQExpr envI a with
      | none => simp [evalQExpr, h1] at h
      | some x =>
        cases h2 : evalQExpr envI b with
        | none => simp [evalQExpr, h1, h2] at h
        | some y =>
          simp [evalQExpr, h1, h2] at h
          subst out
          exact QInterval.mul_sound (iha x h1) (ihb y h2)
  | div a b iha ihb =>
      intro out h
      cases h1 : evalQExpr envI a with
      | none => simp [evalQExpr, h1] at h
      | some x =>
        cases h2 : evalQExpr envI b with
        | none => simp [evalQExpr, h1, h2] at h
        | some y =>
          by_cases hp : 0 < y.lo
          · simp [evalQExpr, h1, h2, hp] at h
            subst out
            have hy := ihb y h2
            have hdiv := QInterval.divPos_sound (iha x h1) hp hy
            simpa [evalQExprReal, div_eq_mul_inv] using hdiv
          · simp [evalQExpr, h1, h2, hp] at h

/-- Decide whether the left expression interval lies strictly above the right one. -/
def evalQExprGt (env : ℕ → QInterval) (left right : QExpr) : Bool :=
  match evalQExpr env left, evalQExpr env right with
  | some l, some r => decide (r.hi < l.lo)
  | _, _ => false

theorem evalQExprGt_sound (envI : ℕ → QInterval) (envR : ℕ → ℝ)
    (henv : ∀ i, QInterval.Contains (envI i) (envR i))
    {left right : QExpr} (hcheck : evalQExprGt envI left right = true) :
    evalQExprReal envR right < evalQExprReal envR left := by
  unfold evalQExprGt at hcheck
  cases hl : evalQExpr envI left with
  | none => simp [hl] at hcheck
  | some l =>
    cases hr : evalQExpr envI right with
    | none => simp [hl, hr] at hcheck
    | some r =>
      simp [hl, hr] at hcheck
      have hsep : r.hi < l.lo := of_decide_eq_true hcheck
      have hleft := evalQExpr_sound envI envR henv left l hl
      have hright := evalQExpr_sound envI envR henv right r hr
      exact lt_of_le_of_lt hright.2 (lt_of_lt_of_le (by exact_mod_cast hsep) hleft.1)

end ASDExplicitGamma.Numerics
