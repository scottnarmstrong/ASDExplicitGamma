/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.ResolventCombine
public import ASDExplicitGamma.Scalar.SmoothFeedbackConsumerArith
public import ASDExplicitGamma.Scalar.Lambda8LoadInputs
public import ASDExplicitGamma.Numerics.Scalar.Lower
public import ASDExplicitGamma.Numerics.Scalar.Frames

/-! The closed-form defect cap of SC-NEW-RESOLVENT-DEFECT, written with the
same arithmetic `consumerL` that SC-SMOOTH-FEEDBACK-GAP uses, and its
identification with the certified numerical tree `quarticDefectExpr`. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar

open ASDExplicitGamma.Numerics.Scalar
open ASDExplicitGamma.Numerics.Mirror

noncomputable section

/-- The weak-face covariance constant `A = 1 + 1.440 s₁ + .285 s₂`,
`s₁ = ρ√31.2`, `s₂ = ρ²√1859.52`, `ρ = 3⁻⁶`. -/
def defectA : ℝ :=
  1 + (36 / 25 : ℝ) * (Real.sqrt (156 / 5 : ℝ) * (1 / 729)) +
    (57 / 200 : ℝ) * (Real.sqrt (46488 / 25 : ℝ) * (1 / 531441))

/-- `Λ = [L + D b_split A √(ξ/2)]²`, with `L = consumerL`; the OLD bank
constant `b` plays all of `b_{-,split}`, `b_{-,total}` as in
SC-SMOOTH-FEEDBACK-GAP, `D = 44/25`. -/
def defectLambda (a5 ξ mStar b ε : ℝ) : ℝ :=
  (consumerL a5 ξ (1 / 2) lambda8DeltaN mStar b ε (76 / 100) (76 / 100) +
    (44 / 25 : ℝ) * b * defectA * Real.sqrt (ξ / 2)) ^ 2

theorem defect_A_eq_certificate :
    defectA = evalReal scalarRealEnv lowerAExpr := by
  simp [defectA, lowerAExpr, lowerS1Expr, lowerS2Expr, evalReal, sc]
  ring

theorem defect_delta_eq_certificate :
    lambda8DeltaN = evalReal scalarRealEnv quarticDeltaExpr := by
  simp [lambda8DeltaN, lambda8Rho, quarticDeltaExpr, evalReal, sc]
  ring

end
end ASDExplicitGamma.Scalar
