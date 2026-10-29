module

public import ASDExplicitGamma.Numerics.Enclosures
public import ASDExplicitGamma.Numerics.QInterval
public import ASDExplicitGamma.Numerics.ExpSqrt
public import ASDExplicitGamma.Numerics.TrigEnclosures

/-!
# End-to-end rational interval certificate

The strict comparison is computed by the rational interval evaluator and its
soundness theorem turns the kernel-checked Boolean into the real inequality.
-/

@[expose] public section

namespace ASDExplicitGamma.Numerics

/-- Rational interval for the logarithm used by the demo. -/
def demoLogThree : QInterval :=
  ⟨1.098612288668109691395245236922, 1.098612288668109691395245236923, by norm_num⟩

/-- The fixed-point product appearing in the margin estimate. -/
def demoLeftExpr : QExpr :=
  .mul (.const (443 / 125)) (.const (31 / 50))

/-- Twice the logarithm, supplied as interval variable zero. -/
def demoRightExpr : QExpr := .mul (.const 2) (.var 0)

def demoIntervalEnv : ℕ → QInterval := fun _ => demoLogThree

noncomputable def demoRealEnv : ℕ → ℝ := fun _ => Real.log 3

theorem demo_log_three_env :
    QInterval.Contains demoLogThree (Real.log 3) := by
  constructor
  · exact_mod_cast log_three_enclosure_30.1
  · exact_mod_cast log_three_enclosure_30.2

/-- Kernel decision for the rational separation of the two expression intervals. -/
theorem demo_interval_check :
    evalQExprGt demoIntervalEnv demoLeftExpr demoRightExpr = true := by
  decide +kernel

/-- The interval evaluator proves the clock-margin inequality over the reals. -/
theorem demo_clock_margin :
    (443 / 125 : ℝ) * (31 / 50) > 2 * Real.log 3 := by
  have h := evalQExprGt_sound demoIntervalEnv demoRealEnv
    (fun _ => demo_log_three_env) demo_interval_check
  simpa [evalQExprReal, demoRealEnv, demoLeftExpr, demoRightExpr] using h

end ASDExplicitGamma.Numerics
