module

public import ASDExplicitGamma.Numerics.Scalar.Mirror

/-! The full-response, inverse-response and all-order wave gates, each at its own parameter tuple.
The formulas use the true sqrt(log 2), not its decimal diagnostic.
-/

@[expose] public section
namespace ASDExplicitGamma.Numerics.Wave
open Mirror

local infixl:65 " +ₑ " => Expr.add
local infixl:70 " *ₑ " => Expr.mul
local infixl:70 " /ₑ " => Expr.divPos
local prefix:max "√ₑ " => Expr.sqrt

def wc (q : ℚ) : Expr := .const q
def waveRho : ℚ := 1/3^41
def fullTau : ℚ := 5*10^15
def inverseTau : ℚ := 10^10
def allOrderTau : ℚ := (218*10^13)*(650/289)*(61/52)
def fullEta : ℚ := 1/(80*(1+fullTau))
def inverseEta : ℚ := 1/(16000000*(1+inverseTau))
def allOrderEta : ℚ := 1/(74*(1+allOrderTau))

/-- The exact source a_b with b=40 and the three q3 tensor traces. -/
def waveAExpr : Expr :=
  √ₑ (wc (312/5)) +ₑ wc waveRho *ₑ
    (wc (3/2) *ₑ √ₑ (wc (92976/25)) +ₑ wc 2 *ₑ √ₑ (.var 0) *ₑ √ₑ (wc (46488/25))) +ₑ
  wc (waveRho^2) *ₑ
    (wc (1/2) *ₑ √ₑ (wc (9389952/25)) +ₑ wc 2 *ₑ √ₑ (.var 0) *ₑ √ₑ (wc (9389952/25)))
def waveEllExpr : Expr := √ₑ (wc (156/5)) +ₑ wc waveRho *ₑ √ₑ (wc (46488/25))
def meanGateExpr (eta : ℚ) : Expr := wc (eta^2*3^80) /ₑ (wc 12 *ₑ (waveAExpr *ₑ waveAExpr))
def tailGateExpr (eta : ℚ) : Expr :=
  wc (eta^2*3^80) /ₑ (wc 60 *ₑ (waveEllExpr *ₑ waveEllExpr) *ₑ wc (1200+(6+11*40/5)/5))

noncomputable def waveA : ℝ :=
  Real.sqrt (312/5)+(waveRho : ℝ)*
    ((3/2)*Real.sqrt (92976/25)+2*Real.sqrt (Real.log 2)*Real.sqrt (46488/25))+
  ((waveRho : ℝ)^2)*
    ((1/2)*Real.sqrt (9389952/25)+2*Real.sqrt (Real.log 2)*Real.sqrt (9389952/25))
noncomputable def waveEll : ℝ := Real.sqrt (156/5)+(waveRho : ℝ)*Real.sqrt (46488/25)
noncomputable def meanGate (eta : ℚ) : ℝ := (eta : ℝ)^2*3^80/(12*waveA^2)
noncomputable def tailGate (eta : ℚ) : ℝ :=
  (eta : ℝ)^2*3^80/(60*waveEll^2*(1200+(6+11*40/5)/5))

def waveGridEnv (_i : ℕ) : QInterval :=
  ⟨0.693147180559945, 0.693147180559946, by norm_num⟩
noncomputable def waveRealEnv (_i : ℕ) : ℝ := Real.log 2

theorem wave_env_sound (i : ℕ) : QInterval.Contains (waveGridEnv i) (waveRealEnv i) :=
  log_two_enclosure

/-- Sixty grid digits retain the tiny η² numerator without losing its lower endpoint. -/
def waveUpperCheck (e : Expr) (u : ℚ) : Bool :=
  match evalGrid 60 25 (by decide) waveGridEnv e with
  | none => false
  | some I => decide (I.hi < u)

theorem wave_upper_sound (e : Expr) (u : ℚ) (hc : waveUpperCheck e u = true) :
    evalReal waveRealEnv e < (u : ℝ) := by
  unfold waveUpperCheck at hc
  cases he : evalGrid 60 25 (by decide) waveGridEnv e with
  | none => simp only [he, Bool.false_eq_true] at hc
  | some I =>
    rw [he] at hc
    exact (evalGrid_sound 60 25 (by decide) waveGridEnv waveRealEnv wave_env_sound e I he).2.trans_lt
      (by exact_mod_cast of_decide_eq_true hc)

theorem mean_gate_formula (eta : ℚ) : evalReal waveRealEnv (meanGateExpr eta) = meanGate eta := by
  norm_num [meanGateExpr, meanGate, waveA, waveAExpr, wc, waveRho, evalReal, waveRealEnv,
    Rat.cast_mul, Rat.cast_pow, ← pow_two]

theorem tail_gate_formula (eta : ℚ) : evalReal waveRealEnv (tailGateExpr eta) = tailGate eta := by
  norm_num [tailGateExpr, tailGate, waveEll, waveEllExpr, wc, waveRho, evalReal, waveRealEnv,
    Rat.cast_mul, Rat.cast_pow, ← pow_two]

theorem wave_gates_kernel_check :
    waveUpperCheck (.neg (meanGateExpr fullEta)) (-(404894/10^9)) = true ∧
    waveUpperCheck (.neg (tailGateExpr fullEta)) (-(404894/10^9)) = true ∧
    waveUpperCheck (.neg (meanGateExpr inverseEta)) (-(253059/10^8)) = true ∧
    waveUpperCheck (.neg (tailGateExpr inverseEta)) (-(253059/10^8)) = true ∧
    waveUpperCheck (.neg (meanGateExpr allOrderEta)) (-(10896/10000)) = true ∧
    waveUpperCheck (.neg (tailGateExpr allOrderEta)) (-(3576034/10^10)) = true ∧
    (17/50000 : ℚ) < 404894/10^9 ∧ (17/50000 : ℚ) < 253059/10^8 ∧
    (17/50000 : ℚ) < 3576034/10^10 ∧ (17/50000 : ℚ) < 1/64 := by
  decide +kernel

theorem mean_gate_lower (eta cap : ℚ) (hc : waveUpperCheck (.neg (meanGateExpr eta)) (-cap) = true) :
    (cap : ℝ) < meanGate eta := by
  have h := wave_upper_sound _ _ hc
  change -evalReal waveRealEnv (meanGateExpr eta) < ((-cap : ℚ) : ℝ) at h
  rw [mean_gate_formula, Rat.cast_neg] at h
  linarith only [h]
theorem tail_gate_lower (eta cap : ℚ) (hc : waveUpperCheck (.neg (tailGateExpr eta)) (-cap) = true) :
    (cap : ℝ) < tailGate eta := by
  have h := wave_upper_sound _ _ hc
  change -evalReal waveRealEnv (tailGateExpr eta) < ((-cap : ℚ) : ℝ) at h
  rw [tail_gate_formula, Rat.cast_neg] at h
  linarith only [h]

/-- The wave gate for the full response: the safe full-response ceiling is above .000404894. -/
theorem full_gates :
    (404894/10^9 : ℝ) < meanGate fullEta ∧ (404894/10^9 : ℝ) < tailGate fullEta ∧
    (17/50000 : ℝ) < 404894/10^9 ∧ (17/50000 : ℝ) < 1/64 := by
  have h := wave_gates_kernel_check
  exact ⟨by simpa using mean_gate_lower _ _ h.1,
    by simpa using tail_gate_lower _ _ h.2.1, by norm_num, by norm_num⟩

/-- The wave gate for the inverse response: preserve its distinct tau=10^10 and ceiling .00253059. -/
theorem inverse_gates :
    (253059/10^8 : ℝ) < meanGate inverseEta ∧ (253059/10^8 : ℝ) < tailGate inverseEta ∧
    (17/50000 : ℝ) < 253059/10^8 ∧ (17/50000 : ℝ) < 1/64 := by
  have h := wave_gates_kernel_check
  exact ⟨by simpa using mean_gate_lower _ _ h.2.2.1,
    by simpa using tail_gate_lower _ _ h.2.2.2.1, by norm_num, by norm_num⟩

/-- The all-order wave gate: its own all-order tuple and the tight .0003576034 ceiling. -/
theorem reset_gates :
    (10896/10000 : ℝ) < meanGate allOrderEta ∧ (3576034/10^10 : ℝ) < tailGate allOrderEta ∧
    (17/50000 : ℝ) < 3576034/10^10 ∧ (17/50000 : ℝ) < 1/64 := by
  have h := wave_gates_kernel_check
  exact ⟨by simpa using mean_gate_lower _ _ h.2.2.2.2.1,
    by simpa using tail_gate_lower _ _ h.2.2.2.2.2.1, by norm_num, by norm_num⟩

end ASDExplicitGamma.Numerics.Wave
