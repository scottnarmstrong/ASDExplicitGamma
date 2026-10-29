module

public import ASDExplicitGamma.Gaussian.RioConditional
public import ASDExplicitGamma.Gaussian.RioNormSquare

/-! # GA-RIO-LP-CONVEXITY: the sharp one-step real Lp inequality -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ASDExplicitGamma.Gaussian

/-- Sharp one-step Lp smoothness for a conditionally centered real increment. The conditional
sigma-field can be σ(S), or any filtration level to which S is adapted. -/
theorem rio_lp_smoothness {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℝ} (hp : 2 ≤ p) {S X : Ω → ℝ}
    (hSm : AEStronglyMeasurable[m] S μ)
    (hS : MemLp S (ENNReal.ofReal p) μ) (hX : MemLp X (ENNReal.ofReal p) μ)
    (hzero : μ[X | m] =ᵐ[μ] 0) :
    (eLpNorm (fun ω => S ω + X ω) (ENNReal.ofReal p) μ).toReal ^ 2 ≤
      (eLpNorm S (ENNReal.ofReal p) μ).toReal ^ 2 +
        (p - 1) * (eLpNorm X (ENNReal.ofReal p) μ).toReal ^ 2 := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hmoment := rio_norm_square_le_of_moment (p := p) hp
    (f := fun t => rioMoment μ p (fun ω => S ω + t * X ω))
    (df := rioMomentDerivative μ p S X) (ddf := rioMomentSecondDerivative μ p S X)
    (L := (eLpNorm X (ENNReal.ofReal p) μ).toReal ^ 2)
    (fun _ => integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)
    (sq_nonneg _) (hasDerivAt_rioMoment μ p S X hp hS hX)
    (hasDerivAt_rioMomentDerivative μ p S X hp hS hX)
    (rioMomentSecondDerivative_le μ p S X hp hS hX)
    (rioMomentDerivative_zero hm μ hp hSm hS hX hzero)
  simp only [one_mul, zero_mul, add_zero] at hmoment
  rw [rio_lpNorm_sq (f := fun ω => S ω + X ω) hp0 (hS.add hX), rio_lpNorm_sq hp0 hS]
  exact hmoment

/-- Literal source form with conditioning on the random variable S itself. -/
theorem rio_lp_smoothness_given_variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℝ} (hp : 2 ≤ p) {S X : Ω → ℝ}
    (hSm : Measurable S) (hS : MemLp S (ENNReal.ofReal p) μ) (hX : MemLp X (ENNReal.ofReal p) μ)
    (hzero : μ[X | MeasurableSpace.comap S (borel ℝ)] =ᵐ[μ] 0) :
    (eLpNorm (fun ω => S ω + X ω) (ENNReal.ofReal p) μ).toReal ^ 2 ≤
      (eLpNorm S (ENNReal.ofReal p) μ).toReal ^ 2 +
        (p - 1) * (eLpNorm X (ENNReal.ofReal p) μ).toReal ^ 2 := by
  apply rio_lp_smoothness hSm.comap_le μ hp ?_ hS hX hzero
  exact (@measurable_iff_comap_le Ω ℝ (MeasurableSpace.comap S (borel ℝ)) (borel ℝ) S).mpr le_rfl
    |>.aestronglyMeasurable

end ASDExplicitGamma.Gaussian
