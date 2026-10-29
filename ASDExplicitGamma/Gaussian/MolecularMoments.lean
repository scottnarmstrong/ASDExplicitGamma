module

public import ASDExplicitGamma.Gaussian.Finite

@[expose] public section

namespace ASDExplicitGamma.Gaussian

open MeasureTheory ProbabilityTheory
open scoped NNReal

private theorem pow_polynomiallyBoundedDerivative (n : ℕ) :
    HasPolynomiallyBoundedDerivative (fun x : ℝ => x ^ (n + 1)) := by
  refine ⟨by fun_prop, (n : ℝ) + 2, by positivity, n + 1, ?_⟩
  intro x
  have hd : deriv (fun y : ℝ => y ^ (n + 1)) x = (n + 1 : ℕ) * x ^ n := by
    simp
  have hp : |x| ^ (n + 1) ≤ (1 + |x|) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg x) (by linarith [abs_nonneg x]) _
  have hpn : |x| ^ n ≤ (1 + |x|) ^ (n + 1) := by
    exact (pow_le_pow_left₀ (abs_nonneg x) (by linarith [abs_nonneg x]) n).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg x] : 1 ≤ 1 + |x|) (Nat.le_succ n))
  have hscaled := mul_le_mul_of_nonneg_left hpn (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ))
  have hc : |((n + 1 : ℕ) : ℝ)| = ((n + 1 : ℕ) : ℝ) := abs_of_nonneg (by positivity)
  simp only [hd, abs_mul, abs_pow, hc]
  push_cast at hscaled ⊢
  nlinarith only [hp, hscaled]

private theorem gaussian_even_moment_step (p : ℕ) :
    (∫ x : ℝ, x ^ (2 * (p + 1)) ∂gaussianReal 0 1) =
      (2 * p + 1 : ℕ) * ∫ x : ℝ, x ^ (2 * p) ∂gaussianReal 0 1 := by
  have hi := integral_id_mul_eq_integral_deriv_gaussianReal (pow_polynomiallyBoundedDerivative (2 * p))
  have hp : (fun x : ℝ => x * x ^ (2 * p + 1)) = fun x => x ^ (2 * (p + 1)) := by
    funext x
    rw [show 2 * (p + 1) = (2 * p + 1) + 1 by omega, pow_succ]
    ring
  have hd : (fun x : ℝ => deriv (fun y : ℝ => y ^ (2 * p + 1)) x) =
      fun x => ((2 * p + 1 : ℕ) : ℝ) * x ^ (2 * p) := by
    funext x
    simp
  rw [hp, hd, integral_const_mul] at hi
  exact hi

/-- The precise Gaussian estimate needed by the p=20 molecular competitor. -/
theorem integral_gaussian_pow_forty_le :
    (∫ x : ℝ, x ^ 40 ∂gaussianReal 0 1) ≤ (39 : ℝ) ^ 20 := by
  have hbound (p : ℕ) (hp : p ≤ 20) :
      (∫ x : ℝ, x ^ (2 * p) ∂gaussianReal 0 1) ≤ (39 : ℝ) ^ p := by
    induction p with
    | zero => simp
    | succ p ih =>
      have hi := ih (by omega)
      rw [gaussian_even_moment_step]
      have hcoeff : (2 * p + 1 : ℝ) ≤ 39 := by exact_mod_cast (show 2 * p + 1 ≤ 39 by omega)
      have hnonneg : (0 : ℝ) ≤ 2 * p + 1 := by positivity
      have hstep := mul_le_mul_of_nonneg_left hi hnonneg
      have hscale := mul_le_mul_of_nonneg_right hcoeff (by positivity : (0 : ℝ) ≤ 39 ^ p)
      push_cast at hstep ⊢
      rw [pow_succ]
      nlinarith only [hstep, hscale]
  exact hbound 20 le_rfl

/-- The fortieth Gaussian moment at an arbitrary variance, with the exact
39 coefficient needed after taking the twentieth root. -/
theorem integral_gaussian_pow_forty_le_variance (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 40 ∂gaussianReal 0 v) ≤ (39 * (v : ℝ)) ^ 20 := by
  have hm : Measure.map (fun x : ℝ => Real.sqrt (v : ℝ) * x) (gaussianReal 0 1) =
      gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    apply Subtype.ext
    exact Real.sq_sqrt v.coe_nonneg
  rw [← hm, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul]
  have hs : Real.sqrt (v : ℝ) ^ 40 = (v : ℝ) ^ 20 := by
    rw [show (40 : ℕ) = 2 * 20 by norm_num, pow_mul, Real.sq_sqrt v.coe_nonneg]
  rw [hs]
  have hh := mul_le_mul_of_nonneg_left integral_gaussian_pow_forty_le
    (by positivity : (0 : ℝ) ≤ (v : ℝ) ^ 20)
  calc
    _ ≤ (v : ℝ) ^ 20 * (39 : ℝ) ^ 20 := hh
    _ = _ := by ring

end ASDExplicitGamma.Gaussian
