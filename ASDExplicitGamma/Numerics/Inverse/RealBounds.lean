module

public import ASDExplicitGamma.Numerics.Inverse.MomentsInverse
public import ASDExplicitGamma.Numerics.Inverse.MomentsFull
public import ASDExplicitGamma.Numerics.Inverse.Tails
public import ASDExplicitGamma.Numerics.Mirror.GridThree
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Analytic soundness of the exponential, root and truncation checks.
See also NU-IN-TRACE-THETA.
-/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse
open ASDExplicitGamma.Numerics

/-- The positive Taylor term controls the complete exponential, including its infinite tail. -/
theorem inv_exp_neg_factorial_bound (x : ℝ) (hx : 0 < x) (n : ℕ) :
    Real.exp (-x) ≤ (Nat.factorial n : ℝ) / x^n := by
  have h := Real.pow_div_factorial_le_exp x hx.le n
  have hf : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  rw [Real.exp_neg]
  calc
    (Real.exp x)⁻¹ ≤ (x^n / (Nat.factorial n : ℝ))⁻¹ :=
      inv_anti₀ (div_pos (pow_pos hx n) hf) h
    _ = (Nat.factorial n : ℝ) / x^n := by rw [inv_div]

/-- Universal truncation estimate; no sampling premise. -/
theorem inv_positive_quadratic (x δ : ℝ) (hδ : 0 < δ) :
    max 0 (x-δ) ≤ x^2/(4*δ) := by
  apply max_le
  · positivity
  · apply (le_div_iff₀ (by positivity : 0 < 4*δ)).2
    nlinarith only [sq_nonneg (x-2*δ)]

/-- Transfer a checked rational upper square into a genuine real radical bound. -/
theorem inv_sqrt_upper {x u : ℚ} (hu : 0 ≤ u) (hx : x < u^2) :
    Real.sqrt (x : ℝ) ≤ (u : ℝ) := by
  apply (Real.sqrt_le_iff).2
  constructor
  · exact_mod_cast hu
  · exact_mod_cast hx.le

/-- Transfer the producer's upward degree-200 floor test. -/
theorem inv_density_floor {q : ℚ}
    (hq : (Nat.factorial 200 : ℚ) < 6000^200*q) :
    Real.exp (-6000) < (q : ℝ) := by
  have hbound := inv_exp_neg_factorial_bound 6000 (by norm_num) 200
  refine lt_of_le_of_lt hbound ?_
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 6000^200)).2
  have h : (Nat.factorial 200 : ℝ) < 6000^200*(q : ℝ) := by exact_mod_cast hq
  simpa only [mul_comm] using h

theorem inv_inverse_density_floor : Real.exp (-6000) < (invInverseQ : ℝ) :=
  inv_density_floor invInverse_floor

theorem inv_full_density_floor : Real.exp (-6000) < (invFullQ : ℝ) :=
  inv_density_floor invFull_floor

/-- The physical factor appearing in every 512-factorial certificate. -/
theorem inv_exp_physical_bound {y : ℝ} (hy : 0 ≤ y) (hy1 : y/1024 < 1) :
    Real.exp y ≤ (1-y/1024)⁻¹^1024 := by
  rw [exp_eq_pow_div y (by norm_num : 0 < (1024 : ℕ))]
  apply pow_le_pow_left₀ (Real.exp_pos _).le
  simpa only [one_div, Nat.cast_ofNat] using Real.exp_bound_div_one_sub_of_interval (by positivity : 0 ≤ y/1024) hy1

/-- Mirror input for the trace-series ratio α² 3^(8γ₀+1/64). -/
def invTraceExponent : QInterval :=
  ⟨1/2-8*(17/50000)-1/64, 1/2-8*(17/50000)-1/64, le_rfl⟩

def invTraceRatioMirror : QInterval :=
  Mirror.powThree 24 25 invTraceExponent (by decide)
    (by decide +kernel) (by decide +kernel)

theorem invTraceRatio_checked : (5/4 : ℚ) < invTraceRatioMirror.lo := by
  decide +kernel

/-- Mirror's positive-power lower bound gives the negative exponent ratio. -/
theorem invTraceRatio_real :
    (3 : ℝ)^(-1/2+8*(17/50000)+1/64 : ℝ) < 4/5 := by
  have hs := Mirror.powThree_sound 24 25 (a := invTraceExponent) (by decide)
    (by decide +kernel) (by decide +kernel)
    (show QInterval.Contains invTraceExponent
      (1/2-8*(17/50000)-1/64 : ℝ) from by
        constructor <;> norm_num [invTraceExponent])
  have hnum : (5/4 : ℝ) < (invTraceRatioMirror.lo : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).2 invTraceRatio_checked
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    exact h
  have hpow : (5/4 : ℝ) < (3 : ℝ)^(1/2-8*(17/50000)-1/64 : ℝ) :=
    hnum.trans_le hs.1
  have he : (-1/2+8*(17/50000)+1/64 : ℝ) = -(1/2-8*(17/50000)-1/64) := by ring
  rw [he, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  have hi := inv_strictAnti₀ (by norm_num : (0 : ℝ) < 5/4) hpow
  norm_num at hi ⊢
  exact hi

/-- Rational powers bound real roots by monotonicity, without a floating approximation. -/
theorem inv_root_upper {x u : ℚ} (hx : 0 ≤ x) (hu : 0 ≤ u) {n : ℕ}
    (hn : n ≠ 0) (h : x < u^n) :
    (x : ℝ)^((n : ℝ)⁻¹) < (u : ℝ) := by
  have hcast : (x : ℝ) < (u : ℝ)^n := by exact_mod_cast h
  have hxcast : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hucast : (0 : ℝ) ≤ u := by exact_mod_cast hu
  have hncast : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hp := Real.rpow_lt_rpow hxcast hcast (inv_pos.mpr hncast)
  simpa only [Real.pow_rpow_inv_natCast hucast hn] using hp

theorem inv_root_lower {x l : ℚ} (hl : 0 ≤ l) {n : ℕ}
    (hn : n ≠ 0) (h : l^n < x) :
    (l : ℝ) < (x : ℝ)^((n : ℝ)⁻¹) := by
  have hlcast : (0 : ℝ) ≤ l := by exact_mod_cast hl
  have hcast : (l : ℝ)^n < (x : ℝ) := by exact_mod_cast h
  have hncast : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hp := Real.rpow_lt_rpow (pow_nonneg hlcast n) hcast (inv_pos.mpr hncast)
  simpa only [Real.pow_rpow_inv_natCast hlcast hn] using hp

/-- Exact source fourth-root enclosure has its usual real meaning. -/
theorem inv_alpha_real :
    (invAlphaLower : ℝ) < (1/3 : ℝ)^(1/4 : ℝ) ∧
    (1/3 : ℝ)^(1/4 : ℝ) < (invAlphaUpper : ℝ) := by
  have hlo := inv_root_lower (le_of_lt invAlpha_bracket.1) (by decide : 4 ≠ 0)
    invAlpha_bracket.2.1
  have hhi := inv_root_upper (by decide +kernel : (0 : ℚ) ≤ 1/3)
    (by decide +kernel : (0 : ℚ) ≤ invAlphaUpper) (by decide : 4 ≠ 0) invAlpha_bracket.2.2
  norm_num only [Nat.cast_ofNat, one_div, Rat.cast_div, Rat.cast_ofNat] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- The elementary clock bound behind the producer's positive rational factors. -/
theorem inv_three_power_bound (t : ℝ) (ht : 0 ≤ t) (hdom : (11/10)*t < 1) :
    (3 : ℝ)^t ≤ 1/(1-(11/10)*t) := by
  have hlog : Real.log 3 ≤ (11/10 : ℝ) :=
    (log_three_enclosure_30.2).trans (by norm_num)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  calc
    Real.exp (Real.log 3*t) ≤ Real.exp ((11/10)*t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hlog ht)
    _ ≤ 1/(1-(11/10)*t) :=
      Real.exp_bound_div_one_sub_of_interval (by positivity) hdom

/-- Mirror lower endpoint needed by the diameter-moment cutoff. -/
def invEulerLower : ℚ := Mirror.expPointLower 24 25 1

theorem invEuler_checked : (2718/1000 : ℚ) < invEulerLower := by
  decide +kernel

theorem invEuler_real : (2718/1000 : ℝ) < Real.exp 1 := by
  have h := (Mirror.expPoint_bounds 24 25 (q := 1) (by decide)
    (by decide +kernel) (by decide +kernel)).1
  have hn : ((2718/1000 : ℚ) : ℝ) < (invEulerLower : ℝ) :=
    (Rat.cast_lt (K := ℝ)).2 invEuler_checked
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hn
  convert hn.trans_le h using 1 <;> norm_num

/-- The common safe chaining factor in the three Gaussian tuples. -/
theorem inv_gate_log2_sqrt : Real.sqrt (Real.log 2) ≤ (5/6 : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · exact (log_two_enclosure.2).trans (by norm_num)

/-- Complete differentiated geometric sum used by the trace correction. -/
theorem inv_trace_geometric_sum :
    (∑' j : ℕ, (1+(j : ℝ))^2*(4/5 : ℝ)^j) = 225 := by
  have hr : ‖(4/5 : ℝ)‖ < 1 := by norm_num
  have hs := hasSum_sq_mul_geometric_of_norm_lt_one hr
  have hl := (hasSum_coe_mul_geometric_of_norm_lt_one hr).mul_left 2
  have hg := hasSum_geometric_of_norm_lt_one hr
  have h := ((hs.add hl).add hg).tsum_eq
  convert h using 1
  · congr 1
    funext j
    ring
  · norm_num

/-- Markov input at every admissible inverse threshold. -/
theorem inv_density_gate {τ : ℝ} (hτ : 10^10 ≤ τ) :
    364*3^80*(3*(61/10)/τ)^12 < (1/10^10 : ℝ) := by
  have hpos : 0 < τ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 10^10) hτ
  calc
    364*3^80*(3*(61/10)/τ)^12 ≤ 364*3^80*(3*(61/10)/10^10)^12 := by
      gcongr
    _ < (1/10^10 : ℝ) := by norm_num

end ASDExplicitGamma.Numerics.Inverse
