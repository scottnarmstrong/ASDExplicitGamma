module

public import ASDExplicitGamma.Numerics.Model.TightInterval
public import ASDExplicitGamma.Numerics.Model.Pi
public import ASDExplicitGamma.Numerics.TrigEnclosures

/-! Certified small-angle Taylor intervals followed by exact double-angle formulas. -/

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
open Mirror

def fromQExpr : QExpr → Expr
  | .const q => .const q
  | .var i => .var i
  | .add a b => .add (fromQExpr a) (fromQExpr b)
  | .mul a b => .mul (fromQExpr a) (fromQExpr b)
  | .div a b => .divPos (fromQExpr a) (fromQExpr b)

theorem fromQExpr_formula (env : ℕ → ℝ) (e : QExpr) :
    evalReal env (fromQExpr e) = evalQExprReal env e := by
  induction e <;> simp only [fromQExpr,evalReal,evalQExprReal, *]

def evalTightQ (G : ℕ) (env : ℕ → QInterval) (e : QExpr) : Option QInterval :=
  evalTight G env (fromQExpr e)

theorem evalTightQ_sound (G : ℕ) (envI : ℕ → QInterval) (envR : ℕ → ℝ)
    (henv : ∀ i, QInterval.Contains (envI i) (envR i)) (e : QExpr) (out : QInterval)
    (he : evalTightQ G envI e = some out) : QInterval.Contains out (evalQExprReal envR e) := by
  have h := evalTight_sound G envI envR henv (fromQExpr e) out he
  rw [fromQExpr_formula] at h
  exact h

theorem expand_interval_error {p e : QInterval} {y z f : ℝ}
    (hp : QInterval.Contains p y) (he : QInterval.Contains e z) (herr : |f-y| ≤ z) :
    QInterval.Contains (expandByError p e) f := by
  have hz : z ≤ (max 0 e.hi : ℚ) := he.2.trans (by exact_mod_cast le_max_right 0 e.hi)
  push_cast at hz
  rw [abs_le] at herr
  change (p.lo : ℝ) ≤ y ∧ y ≤ p.hi at hp
  change ((p.lo-max 0 e.hi : ℚ) : ℝ) ≤ f ∧ f ≤ ((p.hi+max 0 e.hi : ℚ) : ℝ)
  push_cast
  constructor <;> linarith only [hp.1,hp.2,herr.1,herr.2,hz]

/-- Forty Taylor terms on the actual angle (m/(64·3^j))π. -/
def smallTrigIntervals (r : ℚ) : Option (QInterval × QInterval) := do
  let x := rationalPiExpr r
  let sp ← evalTightQ 140 (rationalPiIntervalEnv bflatPiInterval) (sinTaylorExpr x 40)
  let se ← evalTightQ 140 (rationalPiIntervalEnv bflatPiInterval) (sinTermExpr x 40)
  let cp ← evalTightQ 140 (rationalPiIntervalEnv bflatPiInterval) (cosTaylorExpr x 40)
  let ce ← evalTightQ 140 (rationalPiIntervalEnv bflatPiInterval) (cosTailTermExpr x 39)
  return (expandByError sp se,expandByError cp ce)

theorem small_trig_intervals_sound (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1/2)
    (s c : QInterval) (h : smallTrigIntervals r = some (s,c)) :
    QInterval.Contains s (Real.sin ((r : ℝ)*Real.pi)) ∧
    QInterval.Contains c (Real.cos ((r : ℝ)*Real.pi)) := by
  have henv : ∀ i, QInterval.Contains (rationalPiIntervalEnv bflatPiInterval i)
      (rationalPiRealEnv i) := fun _ => bflat_pi_sound
  cases hsp : evalTightQ 140 (rationalPiIntervalEnv bflatPiInterval)
      (sinTaylorExpr (rationalPiExpr r) 40) with
  | none => simp [smallTrigIntervals,hsp] at h
  | some sp =>
    cases hse : evalTightQ 140 (rationalPiIntervalEnv bflatPiInterval)
        (sinTermExpr (rationalPiExpr r) 40) with
    | none => simp [smallTrigIntervals,hsp,hse] at h
    | some se =>
      cases hcp : evalTightQ 140 (rationalPiIntervalEnv bflatPiInterval)
          (cosTaylorExpr (rationalPiExpr r) 40) with
      | none => simp [smallTrigIntervals,hsp,hse,hcp] at h
      | some cp =>
        cases hce : evalTightQ 140 (rationalPiIntervalEnv bflatPiInterval)
            (cosTailTermExpr (rationalPiExpr r) 39) with
        | none => simp [smallTrigIntervals,hsp,hse,hcp,hce] at h
        | some ce =>
          simp [smallTrigIntervals,hsp,hse,hcp,hce] at h
          obtain ⟨rfl,rfl⟩ := h
          have hspR := evalTightQ_sound 140 _ _ henv _ _ hsp
          have hseR := evalTightQ_sound 140 _ _ henv _ _ hse
          have hcpR := evalTightQ_sound 140 _ _ henv _ _ hcp
          have hceR := evalTightQ_sound 140 _ _ henv _ _ hce
          rw [evalQExprReal_sinTaylorExpr] at hspR
          rw [evalQExprReal_sinTermExpr] at hseR
          rw [evalQExprReal_cosTaylorExpr] at hcpR
          rw [evalQExprReal_cosTailTermExpr] at hceR
          norm_num only [rationalPiExpr,rationalPiRealEnv,evalQExprReal] at hspR hseR hcpR hceR
          exact ⟨expand_interval_error hspR hseR (sin_rational_pi_taylor_error hr0 hr1 40),
            expand_interval_error hcpR hceR (cos_rational_pi_taylor_error hr0 hr1 (by decide))⟩

def doubleTrigIntervals (G : ℕ) (p : QInterval × QInterval) : QInterval × QInterval :=
  (tightMul G (gridConstant G 2) (tightMul G p.1 p.2),
    sub G (tightMul G p.2 p.2) (tightMul G p.1 p.1))

def repeatedDoubleIntervals (G : ℕ) (p : QInterval × QInterval) : ℕ → QInterval × QInterval
  | 0 => p
  | n+1 => doubleTrigIntervals G (repeatedDoubleIntervals G p n)

theorem double_trig_intervals_sound (G : ℕ) (s c : QInterval) (x : ℝ)
    (hs : QInterval.Contains s (Real.sin x)) (hc : QInterval.Contains c (Real.cos x)) :
    QInterval.Contains (doubleTrigIntervals G (s,c)).1 (Real.sin (2*x)) ∧
    QInterval.Contains (doubleTrigIntervals G (s,c)).2 (Real.cos (2*x)) := by
  have htwo : QInterval.Contains (gridConstant G 2) (2 : ℝ) := by
    simpa using gridConstant_sound G 2
  have hS := tightMul_sound G htwo (tightMul_sound G hs hc)
  have hC := sub_sound G (tightMul_sound G hc hc) (tightMul_sound G hs hs)
  change QInterval.Contains (tightMul G (gridConstant G 2) (tightMul G s c)) (Real.sin (2*x)) ∧
    QInterval.Contains (sub G (tightMul G c c) (tightMul G s s)) (Real.cos (2*x))
  constructor
  · rw [show Real.sin (2*x) = 2*(Real.sin x*Real.cos x) by rw [Real.sin_two_mul]; ring]
    exact hS
  · rw [show 2*x = x+x by ring, Real.cos_add]
    exact hC

theorem repeated_double_intervals_sound (G : ℕ) (s c : QInterval) (x : ℝ)
    (hs : QInterval.Contains s (Real.sin x)) (hc : QInterval.Contains c (Real.cos x)) (n : ℕ) :
    QInterval.Contains (repeatedDoubleIntervals G (s,c) n).1 (Real.sin (2^n*x)) ∧
    QInterval.Contains (repeatedDoubleIntervals G (s,c) n).2 (Real.cos (2^n*x)) := by
  induction n with
  | zero => simpa only [repeatedDoubleIntervals,pow_zero,one_mul] using And.intro hs hc
  | succ n ih =>
    have h := double_trig_intervals_sound G _ _ (2^n*x) ih.1 ih.2
    simpa only [repeatedDoubleIntervals,pow_succ',mul_assoc] using h

end ASDExplicitGamma.Numerics.Model
