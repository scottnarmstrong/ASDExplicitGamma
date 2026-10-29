module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The exact two-source eigenvalue used by the finite-p raw-trace drift. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

/-- The source coefficient `mu_R / v` from SHEAR (4.1), as the larger
eigenvalue of its projected-source/feedback quadratic form. -/
noncomputable def rawTraceRemainderMu (H0 D0 A B : ℝ) : ℝ :=
  (H0 * A ^ 2 + Real.sqrt (H0 ^ 2 * A ^ 4 + 4 * D0 ^ 2 * A ^ 2 * B ^ 2)) / 2

end ASDExplicitGamma.Inverse
