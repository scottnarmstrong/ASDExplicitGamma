module

public import ASDExplicitGamma.Inverse.StoppedDiameterMomentCaps
public import ASDExplicitGamma.Inverse.WeightedLocalizationMismatch

/-! Literal source budgets for full and localized weighted diameter averages. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- The source rare moment a R_m(T), a=26q. -/
def densityMomentBudget (q : ℝ) (m : ℕ) (T : ℝ) : ℝ :=
  (26*q)*rareMomentPolynomial m T

/-- The exact partial-block Bernstein budget, before N=3^M is optimized. -/
def localizedDensityBudget (q : ℝ) (m : ℕ) (p T : ℝ) (M : ℕ) (a v : ℝ) : ℝ :=
  4*Real.sqrt (p*21^2*densityMomentBudget q (2*m) T*(3:ℝ)^(2*M)*a*v)+
    4*p*21^2*4^m*(3:ℝ)^(M*(m+2))*a

/-- Exact source QSEP localization error, before doubling for centering. -/
def localizationErrorBudget (m : ℕ) (p : ℝ) (M : ℕ) : ℝ :=
  (80*(m:ℝ)*p)^m*(12000:ℝ)^(1/(2*p))*Real.exp (-(3:ℝ)^M/(6*p))

/-- The complete centered full-field budget, retaining the actual layer volume. -/
def fullDensityBudget (q : ℝ) (m : ℕ) (p T : ℝ) (M : ℕ) (a v : ℝ) : ℝ :=
  localizedDensityBudget q m p T M a v+2*localizationErrorBudget m p M*v

theorem density_moment_budget_nonneg (q : ℝ) (hq : 0 ≤ q) (m : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ densityMomentBudget q m T :=
  mul_nonneg (by positivity) (rare_moment_polynomial_nonneg m T hT)

theorem localization_error_budget_nonneg (m : ℕ) (p : ℝ) (hp : 0 ≤ p) (M : ℕ) :
    0 ≤ localizationErrorBudget m p M := by
  unfold localizationErrorBudget
  positivity

end
end ASDExplicitGamma.Inverse
