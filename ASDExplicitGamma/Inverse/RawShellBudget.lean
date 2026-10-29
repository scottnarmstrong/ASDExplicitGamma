module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Exact finite-`p` coefficient summation after the per-shell
moment-chain estimate has supplied its four source rows. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open scoped BigOperators

/-- Summing the `p = 20` per-shell norm rows against the source covariance
budgets gives exactly the coefficient. `v` is the shell variance,
`kappa` the constant-shear coefficient, `mu` the remainder drift mass, and
`q` the combined remainder-bracket coefficient. -/
theorem raw_trace_p20_shell_sum_budget
    (h : ℕ) (e b f : ℝ)
    (v kappa mu q d : ℕ → ℝ)
    (hb : 0 ≤ b) (hf : 0 ≤ f)
    (hV : ∑ i ∈ Finset.range h, v i ≤ (h : ℝ) * e)
    (hK : ∑ i ∈ Finset.range h, v i * kappa i ≤ (521 / 1000 : ℝ) * e)
    (hM : ∑ i ∈ Finset.range h, mu i ≤ (1975 / 1000 : ℝ) * e)
    (hQ : ∑ i ∈ Finset.range h, v i * q i ≤ (1565 / 1000 : ℝ) * e)
    (hrow : ∀ i ∈ Finset.range h,
      d i ≤ v i * (78 * b) +
        (v i * kappa i) * (76 * b + 2 * b * f) +
        mu i * (b ^ 2 * f) +
        (v i * q i) * (38 * b ^ 2 * f)) :
    (∑ i ∈ Finset.range h, d i) ≤
      e * (((78 * (h : ℝ) + 76 * (521 / 1000 : ℝ)) * b) +
        2 * (521 / 1000 : ℝ) * b * f +
        ((1975 / 1000 : ℝ) + 38 * (1565 / 1000 : ℝ)) * b ^ 2 * f) := by
  have hrowSum :
      (∑ i ∈ Finset.range h, d i) ≤
        (78 * b) * (∑ i ∈ Finset.range h, v i) +
          (76 * b + 2 * b * f) * (∑ i ∈ Finset.range h, v i * kappa i) +
          (b ^ 2 * f) * (∑ i ∈ Finset.range h, mu i) +
          (38 * b ^ 2 * f) * (∑ i ∈ Finset.range h, v i * q i) := by
    calc
      (∑ i ∈ Finset.range h, d i) ≤
          ∑ i ∈ Finset.range h,
            (v i * (78 * b) +
              (v i * kappa i) * (76 * b + 2 * b * f) +
              mu i * (b ^ 2 * f) +
              (v i * q i) * (38 * b ^ 2 * f)) :=
        Finset.sum_le_sum (fun i hi => hrow i hi)
      _ = (78 * b) * (∑ i ∈ Finset.range h, v i) +
            (76 * b + 2 * b * f) * (∑ i ∈ Finset.range h, v i * kappa i) +
            (b ^ 2 * f) * (∑ i ∈ Finset.range h, mu i) +
            (38 * b ^ 2 * f) * (∑ i ∈ Finset.range h, v i * q i) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp_rw [← Finset.sum_mul]
        ring
  have hKcoeff : 0 ≤ 76 * b + 2 * b * f := by positivity
  have hMcoeff : 0 ≤ b ^ 2 * f := by positivity
  have hQcoeff : 0 ≤ 38 * b ^ 2 * f := by positivity
  calc
    (∑ i ∈ Finset.range h, d i) ≤
        (78 * b) * (∑ i ∈ Finset.range h, v i) +
          (76 * b + 2 * b * f) * (∑ i ∈ Finset.range h, v i * kappa i) +
          (b ^ 2 * f) * (∑ i ∈ Finset.range h, mu i) +
          (38 * b ^ 2 * f) * (∑ i ∈ Finset.range h, v i * q i) := hrowSum
    _ ≤ (78 * b) * ((h : ℝ) * e) +
          (76 * b + 2 * b * f) * ((521 / 1000 : ℝ) * e) +
          (b ^ 2 * f) * ((1975 / 1000 : ℝ) * e) +
          (38 * b ^ 2 * f) * ((1565 / 1000 : ℝ) * e) := by
      nlinarith [mul_le_mul_of_nonneg_left hV (by positivity : 0 ≤ 78 * b),
        mul_le_mul_of_nonneg_left hK hKcoeff,
        mul_le_mul_of_nonneg_left hM hMcoeff,
        mul_le_mul_of_nonneg_left hQ hQcoeff]
    _ = _ := by ring

end ASDExplicitGamma.Inverse
