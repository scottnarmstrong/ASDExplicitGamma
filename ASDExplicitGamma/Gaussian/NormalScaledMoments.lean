module

public import ASDExplicitGamma.Gaussian.NormalRealMoments

/-! # Literal variance scaling of real Gaussian moments -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Nat

namespace ASDExplicitGamma.Gaussian

/-- A centered real Gaussian is exactly a scaled standard normal, also at zero variance. -/
theorem gaussianReal_eq_map_sqrt (v : ℝ≥0) :
    gaussianReal 0 v = (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt (v : ℝ) * x) := by
  rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  congr 1
  apply Subtype.ext
  exact (Real.sq_sqrt v.property).symm

/-- The real-order square moment of a centered scalar Gaussian is controlled by its variance.
The statement includes zero variance and every real order at least one. -/
theorem gaussianReal_lpNorm_sq_le (v : ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
    (eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal (2 * p)) (gaussianReal 0 v)).toReal ^ 2 ≤
      (2 * p + 2) * (v : ℝ) := by
  let s : ℝ := Real.sqrt (v : ℝ)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hmap : eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal (2 * p))
      (gaussianReal 0 v) = eLpNorm (fun x : ℝ => s * x) (ENNReal.ofReal (2 * p))
        (gaussianReal 0 1) := by
    rw [gaussianReal_eq_map_sqrt]
    exact eLpNorm_map_measure (f := fun x : ℝ => s * x)
      (μ := gaussianReal 0 1) (p := ENNReal.ofReal (2 * p))
      (by fun_prop : AEStronglyMeasurable (id : ℝ → ℝ)
        ((gaussianReal 0 1).map fun x : ℝ => s * x))
      (by fun_prop : AEMeasurable (fun x : ℝ => s * x) (gaussianReal 0 1))
  have hscale : eLpNorm (fun x : ℝ => s * x) (ENNReal.ofReal (2 * p))
      (gaussianReal 0 1) = ENNReal.ofReal s *
        eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal (2 * p)) (gaussianReal 0 1) := by
    rw [show (fun x : ℝ => s * x) = s • (id : ℝ → ℝ) by ext x; simp [smul_eq_mul]]
    rw [eLpNorm_const_smul]
    simp [Real.enorm_of_nonneg hs]
  rw [hmap, hscale]
  have hstandard := normal_real_lpNorm_sq_le hp
  have hnonneg : 0 ≤ (eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal (2 * p))
      (gaussianReal 0 1)).toReal := ENNReal.toReal_nonneg
  have htoReal : (ENNReal.ofReal s * eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal (2 * p))
      (gaussianReal 0 1)).toReal = s *
        (eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal (2 * p)) (gaussianReal 0 1)).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hs]
  rw [htoReal]
  calc
    (s * (eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal (2 * p))
        (gaussianReal 0 1)).toReal) ^ 2
        ≤ s ^ 2 * (2 * p + 2) := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_left hstandard (sq_nonneg s)
    _ = (2 * p + 2) * (v : ℝ) := by
      dsimp [s]
      have hsq : Real.sqrt (v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt v.property
      calc
        Real.sqrt (v : ℝ) ^ 2 * (2 * p + 2) =
            (2 * p + 2) * Real.sqrt (v : ℝ) ^ 2 := by ring
        _ = (2 * p + 2) * (v : ℝ) := congrArg (fun z : ℝ => (2 * p + 2) * z) hsq

/-- The exact fourth moment used for the mean of a spatial L⁴ Gaussian norm. -/
theorem integral_gaussianReal_pow_four (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  rw [gaussianReal_eq_map_sqrt v, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul]
  have he : (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
    simpa using normal_even_moment_eq_doubleFactorial 2 (by norm_num)
  rw [he, show (Real.sqrt (v : ℝ)) ^ 4 = (v : ℝ) ^ 2 by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    exact congrArg (fun r : ℝ => r ^ (2 : ℕ)) (Real.sq_sqrt v.property)]
  ring

/-- The elementary even-moment bound scales with the variance at every natural order. -/
theorem integral_gaussianReal_pow_even_le (v : ℝ≥0) (k : ℕ) :
    (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 v) ≤
      (2 * (k : ℝ)) ^ k * (v : ℝ) ^ k := by
  rw [gaussianReal_eq_map_sqrt v, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul]
  have hstandard := normal_even_moment_le k
  have hscale : Real.sqrt (v : ℝ) ^ (2 * k) = (v : ℝ) ^ k := by
    calc
      Real.sqrt (v : ℝ) ^ (2 * k) = (Real.sqrt (v : ℝ) ^ 2) ^ k := by rw [pow_mul]
      _ = (v : ℝ) ^ k := congrArg (fun z : ℝ => z ^ k) (Real.sq_sqrt v.property)
  rw [hscale]
  calc
    (v : ℝ) ^ k * (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1) ≤
        (v : ℝ) ^ k * (2 * (k : ℝ)) ^ k :=
      mul_le_mul_of_nonneg_left hstandard (pow_nonneg v.property k)
    _ = (2 * (k : ℝ)) ^ k * (v : ℝ) ^ k := by ring
    _ = (2 : ℝ) ^ k * (k : ℝ) ^ k * (v : ℝ) ^ k := by rw [mul_pow]

end ASDExplicitGamma.Gaussian
