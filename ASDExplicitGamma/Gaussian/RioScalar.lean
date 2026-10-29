module

public import Mathlib.Analysis.InnerProductSpace.NormPow
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Scalar differentiation for the sharp real Lp smoothness inequality -/

@[expose] public section

open Set Filter
open scoped Topology

namespace ASDExplicitGamma.Gaussian

/-- The derivative of the signed power is valid at zero as well, including exponent zero. -/
theorem hasDerivAt_abs_rpow_mul {q : ℝ} (hq : 0 ≤ q) (x : ℝ) :
    HasDerivAt (fun y : ℝ => |y| ^ q * y) ((q + 1) * |x| ^ q) x := by
  by_cases hq0 : q = 0
  · subst q
    simpa only [Real.rpow_zero, zero_add, one_mul, id_eq] using hasDerivAt_id' x
  by_cases hx : x = 0
  · subst x
    rw [abs_zero, Real.zero_rpow hq0, mul_zero]
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    have ht : Tendsto (fun y : ℝ => |y| ^ q) (𝓝[≠] 0) (𝓝 0) := by
      simpa only [id_eq, abs_zero, Real.zero_rpow hq0] using
        ((continuousAt_id (x := (0 : ℝ))).abs.rpow_const (Or.inr hq)).tendsto.mono_left nhdsWithin_le_nhds
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [mem_compl_iff, mem_singleton_iff] at hy
    simp only [zero_add, abs_zero, Real.zero_rpow hq0, mul_zero, sub_zero, smul_eq_mul]
    rw [mul_comm (|y| ^ q) y]
    exact (inv_mul_cancel_left₀ hy (|y| ^ q)).symm
  · have ha : 0 < |x| := abs_pos.mpr hx
    have hd := ((hasDerivAt_abs hx).rpow_const (p := q) (Or.inl (ne_of_gt ha))).mul (hasDerivAt_id x)
    have he : |x| ^ (q - 1) * |x| = |x| ^ q := by
      have hh := Real.rpow_add_one ha.ne' (q - 1)
      simpa only [sub_add_cancel] using hh.symm
    have hsign : (SignType.sign x : ℝ) * x = |x| := by
      rcases lt_or_gt_of_ne hx with hx | hx
      · simp [hx, abs_of_neg hx]
      · simp [hx, abs_of_pos hx]
    convert hd using 1
    · rfl
    · simp only [id_eq, mul_one]
      calc
        (q + 1) * |x| ^ q = q * (|x| ^ (q - 1) * |x|) + |x| ^ q := by rw [he]; ring
        _ = ((SignType.sign x : ℝ) * q * |x| ^ (q - 1)) * x + |x| ^ q := by
          calc
            _ = q * |x| ^ (q - 1) * ((SignType.sign x : ℝ) * x) + |x| ^ q := by rw [hsign]; ring
            _ = _ := by ring

/-- The two scalar derivatives used in the parameter-integral proof. -/
theorem hasDerivAt_rio_power_derivative {p : ℝ} (hp : 2 ≤ p) (x : ℝ) :
    HasDerivAt (fun y : ℝ => p * |y| ^ (p - 2) * y)
      (p * (p - 1) * |x| ^ (p - 2)) x := by
  convert (hasDerivAt_abs_rpow_mul (q := p - 2) (by linarith only [hp]) x).const_mul p using 1
  · funext y
    ring
  · ring

/-- Multiplying by the absolute value raises the exponent, including a zero argument. -/
theorem rio_abs_power_mul {p : ℝ} (hp : 2 ≤ p) (y : ℝ) :
    |y| ^ (p - 2) * |y| = |y| ^ (p - 1) := by
  have hh := Real.rpow_add_one' (y := p - 2) (abs_nonneg y) (by linarith only [hp] : p - 2 + 1 ≠ 0)
  convert hh.symm using 1
  congr 1
  ring

/-- Uniform first-derivative domination on a bounded time interval. -/
theorem rio_first_derivative_bound {p y x W : ℝ} (hp : 2 ≤ p) (hW : |y| ≤ W) :
    ‖p * |y| ^ (p - 2) * y * x‖ ≤ p * W ^ (p - 1) * |x| := by
  have hp0 : 0 ≤ p := by linarith only [hp]
  calc
    _ = p * (|y| ^ (p - 2) * |y|) * |x| := by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp0,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) (p - 2))]
      ring
    _ = p * |y| ^ (p - 1) * |x| := by rw [rio_abs_power_mul hp]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg y) hW (by linarith only [hp])) hp0)
      (abs_nonneg x)

/-- Uniform second-derivative domination, with the sharp p(p−1) coefficient. -/
theorem rio_second_derivative_bound {p y x W : ℝ} (hp : 2 ≤ p) (hW : |y| ≤ W) :
    ‖p * (p - 1) * |y| ^ (p - 2) * x ^ 2‖ ≤ p * (p - 1) * W ^ (p - 2) * x ^ 2 := by
  have hc : 0 ≤ p * (p - 1) := mul_nonneg (by linarith only [hp]) (by linarith only [hp])
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hc (Real.rpow_nonneg (abs_nonneg y) _)) (sq_nonneg x))]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg y) hW (by linarith only [hp])) hc) (sq_nonneg x)

/-- Continuity of the first derivative does not exclude zeros of the field. -/
theorem continuous_rio_power_derivative {p : ℝ} (hp : 2 ≤ p) :
    Continuous (fun y : ℝ => p * |y| ^ (p - 2) * y) :=
  (continuous_const.mul (continuous_abs.rpow_const (fun _ => Or.inr (by linarith only [hp])))).mul continuous_id

end ASDExplicitGamma.Gaussian
