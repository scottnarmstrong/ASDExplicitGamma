module
public import ASDExplicitGamma.Numerics.Native.PanelPlan

/-! A compositional monotonicity certificate for positive OLD panel expressions.
Division is accepted only when the denominator is independent of the panel time.
-/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics.Mirror

structure NativeCurveGood (constant : Bool) (f : ℝ → ℝ) : Prop where
  nonneg : ∀ s, 0 ≤ s → 0 ≤ f s
  mono : MonotoneOn f (Set.Ici 0)
  fixed : constant = true → ∀ s t, f s = f t

theorem nativeCurveGood_const (q : ℚ) (hq : 0 ≤ q) : NativeCurveGood true (fun _ : ℝ => (q : ℝ)) := by
  constructor
  · intro s hs; exact_mod_cast hq
  · intro s hs t ht hst; exact le_rfl
  · intro h s t; rfl

theorem NativeCurveGood.add {a b : Bool} {f g : ℝ → ℝ}
    (hf : NativeCurveGood a f) (hg : NativeCurveGood b g) :
    NativeCurveGood (a && b) (fun s => f s+g s) := by
  constructor
  · intro s hs; exact add_nonneg (hf.nonneg s hs) (hg.nonneg s hs)
  · intro s hs t ht hst; exact add_le_add (hf.mono hs ht hst) (hg.mono hs ht hst)
  · intro h s t
    rw [Bool.and_eq_true] at h
    rw [hf.fixed h.1 s t,hg.fixed h.2 s t]

theorem NativeCurveGood.mul {a b : Bool} {f g : ℝ → ℝ}
    (hf : NativeCurveGood a f) (hg : NativeCurveGood b g) :
    NativeCurveGood (a && b) (fun s => f s*g s) := by
  constructor
  · intro s hs; exact mul_nonneg (hf.nonneg s hs) (hg.nonneg s hs)
  · intro s hs t ht hst
    exact mul_le_mul (hf.mono hs ht hst) (hg.mono hs ht hst) (hg.nonneg s hs) (hf.nonneg t ht)
  · intro h s t
    rw [Bool.and_eq_true] at h
    rw [hf.fixed h.1 s t,hg.fixed h.2 s t]

theorem NativeCurveGood.div {a : Bool} {f g : ℝ → ℝ}
    (hf : NativeCurveGood a f) (hg : NativeCurveGood true g) :
    NativeCurveGood a (fun s => f s/g s) := by
  constructor
  · intro s hs; exact div_nonneg (hf.nonneg s hs) (hg.nonneg s hs)
  · intro s hs t ht hst
    change f s/g s ≤ f t/g t
    rw [hg.fixed rfl s t]
    exact div_le_div_of_nonneg_right (hf.mono hs ht hst) (hg.nonneg t ht)
  · intro h s t
    rw [hf.fixed h s t,hg.fixed rfl s t]

theorem NativeCurveGood.sqrt {a : Bool} {f : ℝ → ℝ} (hf : NativeCurveGood a f) :
    NativeCurveGood a (fun s => Real.sqrt (f s)) := by
  constructor
  · intro s hs; exact Real.sqrt_nonneg _
  · intro s hs t ht hst; exact Real.sqrt_le_sqrt (hf.mono hs ht hst)
  · intro h s t; rw [hf.fixed h s t]

theorem NativeCurveGood.exp {a : Bool} {f : ℝ → ℝ} (hf : NativeCurveGood a f) :
    NativeCurveGood a (fun s => Real.exp (f s)) := by
  constructor
  · intro s hs; exact (Real.exp_pos _).le
  · intro s hs t ht hst; exact Real.exp_le_exp.mpr (hf.mono hs ht hst)
  · intro h s t; rw [hf.fixed h s t]

def nativeExprKind (env : ℕ → Bool) : Expr → Option Bool
  | .const q => if 0 ≤ q then some true else none
  | .var i => some (env i)
  | .add x y | .mul x y => do return (← nativeExprKind env x) && (← nativeExprKind env y)
  | .divPos x y => do
      let a ← nativeExprKind env x
      let b ← nativeExprKind env y
      if b then return a else none
  | .sqrt x | .exp x => nativeExprKind env x
  | _ => none

theorem nativeExprKind_sound (env : ℕ → Bool) (values : ℝ → ℕ → ℝ)
    (hv : ∀ i, NativeCurveGood (env i) (fun s => values s i)) :
    ∀ e k, nativeExprKind env e = some k → NativeCurveGood k (fun s => evalReal (values s) e) := by
  intro e
  induction e with
  | const q =>
    intro k h
    by_cases hq : 0 ≤ q
    · simp only [nativeExprKind, hq, reduceIte, Option.some.injEq] at h
      subst k
      exact nativeCurveGood_const q hq
    · simp only [nativeExprKind, hq, reduceIte, reduceCtorEq] at h
  | var i => intro k h; cases Option.some.inj h; exact hv i
  | neg e ih => intro k h; contradiction
  | sub x y ihx ihy => intro k h; contradiction
  | add x y ihx ihy | mul x y ihx ihy =>
    intro k h
    cases hx : nativeExprKind env x with
    | none => simp [nativeExprKind,hx] at h
    | some a =>
      cases hy : nativeExprKind env y with
      | none => simp [nativeExprKind,hx,hy] at h
      | some b =>
        simp [nativeExprKind,hx,hy] at h
        subst k
        first | exact (ihx a hx).add (ihy b hy) | exact (ihx a hx).mul (ihy b hy)
  | divPos x y ihx ihy =>
    intro k h
    cases hx : nativeExprKind env x with
    | none => simp [nativeExprKind,hx] at h
    | some a =>
      cases hy : nativeExprKind env y with
      | none => simp [nativeExprKind,hx,hy] at h
      | some b =>
        cases b with
        | false => simp [nativeExprKind,hx,hy] at h
        | true =>
          simp [nativeExprKind,hx,hy] at h
          subst k
          exact (ihx a hx).div (ihy true hy)
  | sqrt e ih => intro k h; exact (ih k h).sqrt
  | exp e ih => intro k h; exact (ih k h).exp

def nativePlanKinds : List Bool → List Expr → Option (List Bool)
  | stack, [] => some stack
  | stack, e::es =>
    match nativeExprKind (fun i => stack.getD i true) e with
    | none => none
    | some k => nativePlanKinds (k::stack) es

theorem nativePlanKinds_sound (ops : List Expr) (kinds out : List Bool)
    (values : ℝ → List ℝ)
    (hv : ∀ i, NativeCurveGood (kinds.getD i true) (fun s => (values s).getD i 0))
    (h : nativePlanKinds kinds ops = some out) :
    ∀ i, NativeCurveGood (out.getD i true) (fun s => (nativePlanReal (values s) ops).getD i 0) := by
  induction ops generalizing kinds values out with
  | nil =>
    simp only [nativePlanKinds,Option.some.injEq] at h
    subst out
    exact hv
  | cons e es ih =>
    cases he : nativeExprKind (fun i => kinds.getD i true) e with
    | none => simp only [nativePlanKinds,he,reduceCtorEq] at h
    | some k =>
      have hg := nativeExprKind_sound (fun i => kinds.getD i true)
        (fun s i => (values s).getD i 0) hv e k he
      simp only [nativePlanKinds,he] at h
      apply ih (k::kinds) out (fun s => evalReal (fun i => (values s).getD i 0) e::values s) _ h
      intro i
      cases i with
      | zero => exact hg
      | succ i => exact hv i

def nativePlanPositiveCheck (n : ℕ) (ops : List Expr) : Bool :=
  (nativePlanKinds (false::List.replicate n true) ops).isSome

theorem nativePlanPositiveCheck_sound (n : ℕ) (ops : List Expr) (values : ℝ → List ℝ)
    (hv : ∀ i, NativeCurveGood ((false::List.replicate n true).getD i true)
      (fun s => (values s).getD i 0))
    (hc : nativePlanPositiveCheck n ops = true) :
    MonotoneOn (fun s => (nativePlanReal (values s) ops).getD 0 0) (Set.Ici 0) := by
  cases he : nativePlanKinds (false::List.replicate n true) ops with
  | none => simp only [nativePlanPositiveCheck,he,Option.isSome_none,Bool.false_eq_true] at hc
  | some out => exact (nativePlanKinds_sound ops _ out values hv he 0).mono

end ASDExplicitGamma.Numerics.Native
