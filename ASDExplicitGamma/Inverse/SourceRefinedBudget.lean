module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Exact finite-`p` coefficient summation after the per-shell
moment-chain estimate has suppliecost its four source rows. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open scoped BigOperators

/-- Summing the `p = 20` per-shell norm rows against arbitrary nonnegative
factor payments gives their literal covariance-cap coefficient. `v` is the shell variance,
`kappa` the constant-shear coefficient, `mu` the remainder drift mass, and
`q` the combined remainder-bracket coefficient. -/
theorem source_refined_shell_sum_budget_of_covariance_caps
    (h : ℕ) (e b d u1 u2 K M Q : ℝ)
    (v kappa mu q cost : ℕ → ℝ)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hu1 : 0 ≤ u1) (hu2 : 0 ≤ u2)
    (hV : ∑ i ∈ Finset.range h, v i ≤ (h : ℝ) * e)
    (hK : ∑ i ∈ Finset.range h, v i * kappa i ≤ K * e)
    (hM : ∑ i ∈ Finset.range h, mu i ≤ M * e)
    (hQ : ∑ i ∈ Finset.range h, v i * q i ≤ Q * e)
    (hrow : ∀ i ∈ Finset.range h,
      cost i ≤ v i * (39 * d) +
        (v i * kappa i) * (38 * d + 2 * b * u1) +
        mu i * (b ^ 2 * u2) +
        (v i * q i) * (38 * b ^ 2 * u2)) :
    (∑ i ∈ Finset.range h, cost i) ≤
      e * (((39 * (h : ℝ) + 38 * K) * d) +
        2 * K * b * u1 +
        (M + 38 * Q) * b ^ 2 * u2) := by
  have hrowSum :
      (∑ i ∈ Finset.range h, cost i) ≤
        (39 * d) * (∑ i ∈ Finset.range h, v i) +
          (38 * d + 2 * b * u1) * (∑ i ∈ Finset.range h, v i * kappa i) +
          (b ^ 2 * u2) * (∑ i ∈ Finset.range h, mu i) +
          (38 * b ^ 2 * u2) * (∑ i ∈ Finset.range h, v i * q i) := by
    calc
      (∑ i ∈ Finset.range h, cost i) ≤
          ∑ i ∈ Finset.range h,
            (v i * (39 * d) +
              (v i * kappa i) * (38 * d + 2 * b * u1) +
              mu i * (b ^ 2 * u2) +
              (v i * q i) * (38 * b ^ 2 * u2)) :=
        Finset.sum_le_sum (fun i hi => hrow i hi)
      _ = (39 * d) * (∑ i ∈ Finset.range h, v i) +
            (38 * d + 2 * b * u1) * (∑ i ∈ Finset.range h, v i * kappa i) +
            (b ^ 2 * u2) * (∑ i ∈ Finset.range h, mu i) +
            (38 * b ^ 2 * u2) * (∑ i ∈ Finset.range h, v i * q i) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp_rw [← Finset.sum_mul]
        ring
  have hKcoeff : 0 ≤ 38 * d + 2 * b * u1 := by positivity
  have hMcoeff : 0 ≤ b ^ 2 * u2 := by positivity
  have hQcoeff : 0 ≤ 38 * b ^ 2 * u2 := by positivity
  calc
    (∑ i ∈ Finset.range h, cost i) ≤
        (39 * d) * (∑ i ∈ Finset.range h, v i) +
          (38 * d + 2 * b * u1) * (∑ i ∈ Finset.range h, v i * kappa i) +
          (b ^ 2 * u2) * (∑ i ∈ Finset.range h, mu i) +
          (38 * b ^ 2 * u2) * (∑ i ∈ Finset.range h, v i * q i) := hrowSum
    _ ≤ (39 * d) * ((h : ℝ) * e) +
          (38 * d + 2 * b * u1) * (K * e) +
          (b ^ 2 * u2) * (M * e) +
          (38 * b ^ 2 * u2) * (Q * e) := by
      nlinarith [mul_le_mul_of_nonneg_left hV (by positivity : 0 ≤ 39 * d),
        mul_le_mul_of_nonneg_left hK hKcoeff,
        mul_le_mul_of_nonneg_left hM hMcoeff,
        mul_le_mul_of_nonneg_left hQ hQcoeff]
    _ = _ := by ring


/-- Summing the `p = 20` per-shell norm rows against the source covariance
budgets gives exactly the coefficient. `v` is the shell variance,
`kappa` the constant-shear coefficient, `mu` the remainder drift mass, and
`q` the combined remainder-bracket coefficient. -/
theorem source_refined_shell_sum_budget
    (h : ℕ) (e b d u1 u2 : ℝ)
    (v kappa mu q cost : ℕ → ℝ)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hu1 : 0 ≤ u1) (hu2 : 0 ≤ u2)
    (hV : ∑ i ∈ Finset.range h, v i ≤ (h : ℝ) * e)
    (hK : ∑ i ∈ Finset.range h, v i * kappa i ≤ (521 / 1000 : ℝ) * e)
    (hM : ∑ i ∈ Finset.range h, mu i ≤ (1975 / 1000 : ℝ) * e)
    (hQ : ∑ i ∈ Finset.range h, v i * q i ≤ (1565 / 1000 : ℝ) * e)
    (hrow : ∀ i ∈ Finset.range h,
      cost i ≤ v i * (39 * d) +
        (v i * kappa i) * (38 * d + 2 * b * u1) +
        mu i * (b ^ 2 * u2) +
        (v i * q i) * (38 * b ^ 2 * u2)) :
    (∑ i ∈ Finset.range h, cost i) ≤
      e * (((39 * (h : ℝ) + 38 * (521 / 1000 : ℝ)) * d) +
        2 * (521 / 1000 : ℝ) * b * u1 +
        ((1975 / 1000 : ℝ) + 38 * (1565 / 1000 : ℝ)) * b ^ 2 * u2) := by
  have hrowSum :
      (∑ i ∈ Finset.range h, cost i) ≤
        (39 * d) * (∑ i ∈ Finset.range h, v i) +
          (38 * d + 2 * b * u1) * (∑ i ∈ Finset.range h, v i * kappa i) +
          (b ^ 2 * u2) * (∑ i ∈ Finset.range h, mu i) +
          (38 * b ^ 2 * u2) * (∑ i ∈ Finset.range h, v i * q i) := by
    calc
      (∑ i ∈ Finset.range h, cost i) ≤
          ∑ i ∈ Finset.range h,
            (v i * (39 * d) +
              (v i * kappa i) * (38 * d + 2 * b * u1) +
              mu i * (b ^ 2 * u2) +
              (v i * q i) * (38 * b ^ 2 * u2)) :=
        Finset.sum_le_sum (fun i hi => hrow i hi)
      _ = (39 * d) * (∑ i ∈ Finset.range h, v i) +
            (38 * d + 2 * b * u1) * (∑ i ∈ Finset.range h, v i * kappa i) +
            (b ^ 2 * u2) * (∑ i ∈ Finset.range h, mu i) +
            (38 * b ^ 2 * u2) * (∑ i ∈ Finset.range h, v i * q i) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp_rw [← Finset.sum_mul]
        ring
  have hKcoeff : 0 ≤ 38 * d + 2 * b * u1 := by positivity
  have hMcoeff : 0 ≤ b ^ 2 * u2 := by positivity
  have hQcoeff : 0 ≤ 38 * b ^ 2 * u2 := by positivity
  calc
    (∑ i ∈ Finset.range h, cost i) ≤
        (39 * d) * (∑ i ∈ Finset.range h, v i) +
          (38 * d + 2 * b * u1) * (∑ i ∈ Finset.range h, v i * kappa i) +
          (b ^ 2 * u2) * (∑ i ∈ Finset.range h, mu i) +
          (38 * b ^ 2 * u2) * (∑ i ∈ Finset.range h, v i * q i) := hrowSum
    _ ≤ (39 * d) * ((h : ℝ) * e) +
          (38 * d + 2 * b * u1) * ((521 / 1000 : ℝ) * e) +
          (b ^ 2 * u2) * ((1975 / 1000 : ℝ) * e) +
          (38 * b ^ 2 * u2) * ((1565 / 1000 : ℝ) * e) := by
      nlinarith [mul_le_mul_of_nonneg_left hV (by positivity : 0 ≤ 39 * d),
        mul_le_mul_of_nonneg_left hK hKcoeff,
        mul_le_mul_of_nonneg_left hM hMcoeff,
        mul_le_mul_of_nonneg_left hQ hQcoeff]
    _ = _ := by ring

end ASDExplicitGamma.Inverse
