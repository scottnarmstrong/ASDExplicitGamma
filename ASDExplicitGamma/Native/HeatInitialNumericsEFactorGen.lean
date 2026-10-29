module

public import ASDExplicitGamma.Native.HeatInitialNumericsStructGen
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! The per-shell variance factor cap `(9/2) γ 3^(2 γ ns) ≤ e` for every
`γ ≤ γ₀`, reduced to a rational inequality in `ns`: monotonicity in `γ`, then an
exponential Taylor bound with the rational upper bound `log 3 < 1.0986122888`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Algsuperdiff.Frozen.Assumptions

/-- The rational Taylor-type upper bound for `(9/2) γ₀ 3^(2 γ₀ ns)`. -/
def nativeHeatGenEUpper (ns : ℕ) : ℚ :=
  let y : ℚ := (10986122888 / 10000000000 : ℚ) * (17 * (ns : ℚ) / 25000)
  (9 / 2 : ℚ) * (17 / 50000 : ℚ) *
    ((∑ m ∈ Finset.range 6, y ^ m / (m.factorial : ℚ)) + y ^ 6 * 7 / (720 * 6))

/-- `3^x ≤` the Taylor bound, for `0 ≤ x ≤ 1/2`. -/
theorem nativeHeat_three_rpow_le_taylor (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    (3 : ℝ) ^ x ≤
      (∑ m ∈ Finset.range 6, (((10986122888 / 10000000000 : ℝ) * x) ^ m / (m.factorial : ℝ))) +
        ((10986122888 / 10000000000 : ℝ) * x) ^ 6 * 7 / (720 * 6) := by
  have hlog : Real.log 3 ≤ (10986122888 / 10000000000 : ℝ) := by
    have := Real.log_three_lt_d9
    norm_num at this ⊢
    linarith
  have hy0 : 0 ≤ (10986122888 / 10000000000 : ℝ) * x := by positivity
  have hy1 : (10986122888 / 10000000000 : ℝ) * x ≤ 1 := by nlinarith
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  have h1 : Real.log 3 * x ≤ (10986122888 / 10000000000 : ℝ) * x :=
    mul_le_mul_of_nonneg_right hlog hx0
  refine (Real.exp_le_exp.mpr h1).trans ?_
  have := Real.exp_bound' hy0 hy1 (n := 6) (by norm_num)
  refine this.trans (le_of_eq ?_)
  norm_num [Nat.factorial]

theorem nativeHeat_efactor_of_check (ns : ℕ) (hns : ns ≤ 160)
    (hcheck : nativeHeatGenEUpper ns ≤ (nativeHeatOldRowGen ns).e) :
    ∀ γ : ℝ, 0 ≤ γ → γ ≤ gammaZero →
      (9 / 2 : ℝ) * γ * (3 : ℝ) ^ (2 * γ * (ns : ℝ)) ≤
        ((nativeHeatOldRowGen ns).e : ℝ) := by
  intro γ hγ0 hγ
  have hg0 : gammaZero = 17 / 50000 := by norm_num [gammaZero]
  rw [hg0] at hγ
  have hns' : (ns : ℝ) ≤ 160 := by exact_mod_cast hns
  have hns0 : (0 : ℝ) ≤ ns := Nat.cast_nonneg ns
  have hmono : (9 / 2 : ℝ) * γ * (3 : ℝ) ^ (2 * γ * (ns : ℝ)) ≤
      (9 / 2 : ℝ) * (17 / 50000 : ℝ) * (3 : ℝ) ^ (2 * (17 / 50000 : ℝ) * (ns : ℝ)) := by
    have hp : (3 : ℝ) ^ (2 * γ * (ns : ℝ)) ≤ (3 : ℝ) ^ (2 * (17 / 50000 : ℝ) * (ns : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    have h1 : (9 / 2 : ℝ) * γ ≤ (9 / 2 : ℝ) * (17 / 50000 : ℝ) := by linarith
    exact mul_le_mul h1 hp (by positivity) (by positivity)
  have hx : 2 * (17 / 50000 : ℝ) * (ns : ℝ) = 17 * (ns : ℝ) / 25000 := by ring
  rw [hx] at hmono
  have htay := nativeHeat_three_rpow_le_taylor (17 * (ns : ℝ) / 25000) (by positivity)
    (by linarith)
  have hcheckR : (nativeHeatGenEUpper ns : ℝ) ≤ ((nativeHeatOldRowGen ns).e : ℝ) := by
    exact_mod_cast hcheck
  refine hmono.trans (le_trans ?_ hcheckR)
  have hpos : (0 : ℝ) ≤ (9 / 2 : ℝ) * (17 / 50000 : ℝ) := by norm_num
  have := mul_le_mul_of_nonneg_left htay hpos
  refine this.trans (le_of_eq ?_)
  unfold nativeHeatGenEUpper
  push_cast
  ring

end ASDExplicitGamma.Native
