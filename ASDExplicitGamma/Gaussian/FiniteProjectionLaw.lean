module

public import ASDExplicitGamma.Gaussian.ZeroPaddedOrthonormal
public import ASDExplicitGamma.Gaussian.SeriesHeat
public import Mathlib.Probability.Independence.InfinitePi

/-! # Exact finite Gaussian laws of the retained series coordinates -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ASDExplicitGamma.Gaussian

/-- The first N independent coordinates have exactly the standard finite product law. -/
theorem map_standardGaussian_firstCoordinates (N : ℕ) :
    standardGaussianInfinitePi.map (fun ω : ℕ → ℝ => fun i : Fin N => ω i.val) =
      standardGaussianPi N := by
  rw [standardGaussianInfinitePi,
    Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
  rfl

/-- Integration of any measurable finite-coordinate test uses the exact finite product law. -/
theorem integral_standardGaussian_firstCoordinates (N : ℕ) (F : (Fin N → ℝ) → ℝ)
    (hF : AEStronglyMeasurable F (standardGaussianPi N)) :
    (∫ ω : ℕ → ℝ, F (fun i : Fin N => ω i.val) ∂standardGaussianInfinitePi) =
      ∫ x, F x ∂standardGaussianPi N := by
  rw [← map_standardGaussian_firstCoordinates N] at hF ⊢
  exact (integral_map (measurable_pi_iff.mpr fun i : Fin N =>
    measurable_pi_apply i.val).aemeasurable hF).symm

/-- The same exact finite-coordinate law preserves every probability Lᵖ seminorm. -/
theorem eLpNorm_standardGaussian_firstCoordinates (N : ℕ) (F : (Fin N → ℝ) → ℝ)
    (hF : AEStronglyMeasurable F (standardGaussianPi N)) (p : ENNReal) :
    eLpNorm (fun ω : ℕ → ℝ => F (fun i : Fin N => ω i.val)) p standardGaussianInfinitePi =
      eLpNorm F p (standardGaussianPi N) := by
  rw [← map_standardGaussian_firstCoordinates N] at hF ⊢
  exact (eLpNorm_map_measure hF (measurable_pi_iff.mpr fun i : Fin N =>
    measurable_pi_apply i.val).aemeasurable).symm

end ASDExplicitGamma.Gaussian
