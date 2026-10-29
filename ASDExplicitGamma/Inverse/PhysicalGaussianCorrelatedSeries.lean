module

public import ASDExplicitGamma.Inverse.PhysicalGaussianCorrelatedDensity
public import ASDExplicitGamma.Inverse.StoppedResetDensityBudgets
public import ASDExplicitGamma.Inverse.StoppedDensitySumNorm

/-! Actual correlated physical wave/density errors: complete deterministic-height
and layer sums before selection, retaining the density order p. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Literal correlated source error on one deterministic height and layer. -/
def physicalCorrelatedDensityTerm (A : ABKModel 2) (Q : TriadicCube 2) (N : ℤ) (H0 : ℕ)
    (τ η q T S a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ) (j : Fin 2) (hk : ℕ × ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  (S+1)*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)^j.val*
    ∑ e : Fin 3, physicalResetWave A Q N H0 a c weights hk ω*
      Real.sqrt (resetDensityExcess A Q H0 τ η q T 4 hk e ω)

end
end ASDExplicitGamma.Inverse
