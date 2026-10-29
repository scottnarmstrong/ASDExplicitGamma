module

public import ASDExplicitGamma.Gaussian.NormMGF
public import ASDExplicitGamma.Gaussian.PositiveExponentialMoment

/-! # Real-order fluctuations of finite Gaussian Banach norms -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ASDExplicitGamma.Gaussian

/-- The real-order positive fluctuation estimate used in GA-WHOLE-ROOT. It follows from the
sharp MGF bound and elementary power/exponential comparison, without a Gamma-function estimate. -/
theorem positivePart_centered_norm_lpNorm_sq_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [SecondCountableTopology E] {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] E) {L p : ℝ}
    (hL : 0 < L) (hp : 0 < p) (hT : ‖T‖ ≤ L) :
    MemLp (fun x : Fin n → ℝ => max (‖T (WithLp.toLp 2 x)‖ -
      ∫ y : Fin n → ℝ, ‖T (WithLp.toLp 2 y)‖ ∂standardGaussianPi n) 0)
      (ENNReal.ofReal p) (standardGaussianPi n) ∧
    (eLpNorm (fun x : Fin n → ℝ => max (‖T (WithLp.toLp 2 x)‖ -
      ∫ y : Fin n → ℝ, ‖T (WithLp.toLp 2 y)‖ ∂standardGaussianPi n) 0)
      (ENNReal.ofReal p) (standardGaussianPi n)).toReal ^ 2 ≤ p * L ^ 2 := by
  let c := L * Real.sqrt p
  have hc : 0 < c := mul_pos hL (Real.sqrt_pos.mpr hp)
  have he : (p / c) ^ 2 * L ^ 2 / 2 = p / 2 := by
    dsimp only [c]
    rw [div_pow, mul_pow, Real.sq_sqrt hp.le]
    field_simp
  have hmgf := integral_exp_centered_norm_le T hL (div_nonneg hp.le hc.le) hT
  rw [he] at hmgf
  have hbound : (∫ x : Fin n → ℝ, Real.exp ((p / c) * (‖T (WithLp.toLp 2 x)‖ -
      ∫ y : Fin n → ℝ, ‖T (WithLp.toLp 2 y)‖ ∂standardGaussianPi n)) ∂standardGaussianPi n) ≤
      Real.exp p := hmgf.2.trans (Real.exp_le_exp.mpr (by linarith only [hp]))
  have hm : Continuous (fun x : Fin n → ℝ => ‖T (WithLp.toLp 2 x)‖ -
      ∫ y : Fin n → ℝ, ‖T (WithLp.toLp 2 y)‖ ∂standardGaussianPi n) := by fun_prop
  have hh := positivePart_lpNorm_sq_le_of_exp (standardGaussianPi n) hp hc
    hm.aestronglyMeasurable hmgf.1 hbound
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  dsimp only [c]
  rw [mul_pow, Real.sq_sqrt hp.le, mul_comm]

end ASDExplicitGamma.Gaussian
