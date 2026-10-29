module

public import ASDExplicitGamma.Native.BoundaryChargeDegree

/-! Checked degree inference for the exact boundary-fixed OLD panel program. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.Native ASDExplicitGamma.Numerics.Mirror
noncomputable section

/-- Degree inference accepts only nonnegative constants, positive algebra,
even-degree square roots and exactly fixed denominators. -/
def nativeBoundaryExprDegree (env : ℕ → NativeBoundaryDegreeTag) : Expr → Option NativeBoundaryDegreeTag
  | .const q => if 0 ≤ q then some ⟨0,true⟩ else none
  | .var i => some (env i)
  | .add x y => do
      let a ← nativeBoundaryExprDegree env x
      let b ← nativeBoundaryExprDegree env y
      return ⟨min a.degree b.degree,a.fixed && b.fixed⟩
  | .mul x y => do
      let a ← nativeBoundaryExprDegree env x
      let b ← nativeBoundaryExprDegree env y
      return ⟨a.degree+b.degree,a.fixed && b.fixed⟩
  | .divPos x y => do
      let a ← nativeBoundaryExprDegree env x
      let b ← nativeBoundaryExprDegree env y
      if b.fixed then return ⟨a.degree,a.fixed && b.fixed⟩ else none
  | .sqrt x => do
      let a ← nativeBoundaryExprDegree env x
      if a.degree%2=0 then return ⟨a.degree/2,a.fixed⟩ else none
  | _ => none

/-- Every inferred degree is a valid actual-to-endpoint inequality. -/
theorem native_boundary_expr_degree_sound (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (env : ℕ → NativeBoundaryDegreeTag) (values endpoint : ℕ → ℝ)
    (hv : ∀ i, NativeBoundaryDegreeControl z (env i) (values i) (endpoint i)) :
    ∀ e k, nativeBoundaryExprDegree env e=some k →
      NativeBoundaryDegreeControl z k (evalReal values e) (evalReal endpoint e) := by
  intro e
  induction e with
  | const q =>
    intro k h
    by_cases hq : 0 ≤ q
    · simp only [nativeBoundaryExprDegree,hq,reduceIte,Option.some.injEq] at h
      subst k
      exact native_boundary_degree_const z q hq
    · simp only [nativeBoundaryExprDegree,hq,reduceIte,reduceCtorEq] at h
  | var i => intro k h; cases Option.some.inj h; exact hv i
  | neg e ih => intro k h; contradiction
  | sub x y ihx ihy => intro k h; contradiction
  | exp e ih => intro k h; contradiction
  | add x y ihx ihy | mul x y ihx ihy =>
    intro k h
    cases hx : nativeBoundaryExprDegree env x with
    | none => simp [nativeBoundaryExprDegree,hx] at h
    | some a =>
      cases hy : nativeBoundaryExprDegree env y with
      | none => simp [nativeBoundaryExprDegree,hx,hy] at h
      | some b =>
        simp [nativeBoundaryExprDegree,hx,hy] at h
        subst k
        first | exact (ihx a hx).add (ihy b hy) hz0 hz1 | exact (ihx a hx).mul (ihy b hy) hz0
  | divPos x y ihx ihy =>
    intro k h
    cases hx : nativeBoundaryExprDegree env x with
    | none => simp [nativeBoundaryExprDegree,hx] at h
    | some a =>
      cases hy : nativeBoundaryExprDegree env y with
      | none => simp [nativeBoundaryExprDegree,hx,hy] at h
      | some b =>
        cases hb : b.fixed with
        | false => simp [nativeBoundaryExprDegree,hx,hy,hb] at h
        | true =>
          simp [nativeBoundaryExprDegree,hx,hy,hb] at h
          subst k
          simpa only [hb,Bool.and_true,evalReal] using (ihx a hx).div (ihy b hy) hb
  | sqrt e ih =>
    intro k h
    cases he : nativeBoundaryExprDegree env e with
    | none => simp [nativeBoundaryExprDegree,he] at h
    | some a =>
      by_cases ha : a.degree%2=0
      · simp [nativeBoundaryExprDegree,he,ha] at h
        subst k
        exact (ih a he).sqrt hz0 ha
      · simp [nativeBoundaryExprDegree,he,ha] at h

end
end ASDExplicitGamma.Native
