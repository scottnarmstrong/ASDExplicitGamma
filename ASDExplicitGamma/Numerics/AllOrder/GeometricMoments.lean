module

public import ASDExplicitGamma.Numerics.AllOrder.CirGates
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.IntervalCases

/-! The complete normalized depth moments in NU-AO-BULK-HISTORY. -/

@[expose] public section
namespace ASDExplicitGamma.Numerics.AllOrder

theorem geometric_base_lt_quarter : (3 : ℝ)^(-(11/8 : ℝ)) < 1/4 := by
  apply lt_of_pow_lt_pow_left₀ 8 (by norm_num : (0 : ℝ) ≤ 1/4)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- Convexity at the endpoints 0 and 1 gives the source denominator ≥3s/4. -/
theorem geometric_denominator (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (3/4 : ℝ)*s ≤ 1-(3 : ℝ)^(-(11/8 : ℝ)*s) := by
  let u := -(11/8 : ℝ)*Real.log 3
  have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ u)
    (sub_nonneg.mpr hs1) hs (by ring : (1-s)+s = 1)
  have he : Real.exp u ≤ (1/4 : ℝ) := by
    have hh := geometric_base_lt_quarter.le
    rw [Real.rpow_def_of_pos (by norm_num)] at hh
    simpa only [u, mul_comm] using hh
  have hm := mul_le_mul_of_nonneg_left he hs
  have hpower : (3 : ℝ)^(-(11/8 : ℝ)*s) = Real.exp (s*u) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    dsimp [u]
    ring
  rw [hpower]
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
  linarith only [hc,hm]

/-- The normalization mass costs at most 16/11, before weakening it to 3/2. -/
theorem geometric_normalization (s : ℝ) :
    1-(3 : ℝ)^(-2*s) ≤ (16/11 : ℝ)*(1-(3 : ℝ)^(-(11/8 : ℝ)*s)) := by
  let y := (3 : ℝ)^(-(11/8 : ℝ)*s)
  have hy : 0 ≤ y := Real.rpow_nonneg (by norm_num) _
  have h := one_add_mul_self_le_rpow_one_add (s := y-1) (p := (16/11 : ℝ))
    (by linarith only [hy]) (by norm_num)
  have he : y^(16/11 : ℝ) = (3 : ℝ)^(-2*s) := by
    dsimp [y]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  rw [show 1+(y-1) = y by ring, he] at h
  dsimp [y] at h
  linarith only [h]

/-- The elementary power-series factorial bounds for exactly the four moments consumed. -/
theorem geometric_power_sum_le (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1)
    (k : ℕ) (hk : k ≤ 3) :
    (∑' n : ℕ, (n : ℝ)^k*x^n) ≤ (k.factorial : ℝ)/(1-x)^(k+1) := by
  have hn : ‖x‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hx] using hx1
  rw [tsum_pow_mul_geometric_of_norm_lt_one k hn]
  have hd : 0 < 1-x := sub_pos.mpr hx1
  have hx2 : x^2 ≤ 1 := pow_le_one₀ hx hx1.le
  have hx3 : x^3 ≤ 1 := pow_le_one₀ hx hx1.le
  interval_cases k <;> norm_num [Finset.sum_range_succ, Nat.stirlingSecond, Nat.factorial]
  · calc
      x/(1-x)^2 ≤ 1/(1-x)^2 := div_le_div_of_nonneg_right hx1.le (pow_nonneg hd.le _)
      _ = _ := by rw [one_div]
  · have he : x/(1-x)^2+2*x^2/(1-x)^3 = (x+x^2)/(1-x)^3 := by
      field_simp
      ring
    rw [he]
    exact div_le_div_of_nonneg_right (by linarith only [hx1.le,hx2]) (pow_nonneg hd.le _)
  · have hp : x+4*x^2+x^3 ≤ 6 := by linarith only [hx1.le,hx2,hx3]
    have he : x/(1-x)^2+6*x^2/(1-x)^3+6*x^3/(1-x)^4 =
        (x+4*x^2+x^3)/(1-x)^4 := by field_simp; ring
    rw [he]
    exact div_le_div_of_nonneg_right hp (pow_nonneg hd.le _)

/-- Abstract normalized moment estimate, with its two scalar geometric inputs explicit. -/
theorem normalized_moment_bound (a x s : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) (hx1 : x < 1)
    (hs : 0 < s) (hmass : a/(1-x) ≤ 3/2) (hgap : (3/4)*s ≤ 1-x)
    (k : ℕ) (hk : k ≤ 3) :
    a*(∑' n : ℕ, (n : ℝ)^k*x^n) ≤ (3/2 : ℝ)*(k.factorial : ℝ)*(4/(3*s))^k := by
  have hd : 0 < 1-x := sub_pos.mpr hx1
  have hu : 1/(1-x) ≤ 4/(3*s) := by
    apply (div_le_div_iff₀ hd (by positivity : (0 : ℝ) < 3*s)).mpr
    linarith only [hgap]
  calc
    a*(∑' n : ℕ, (n : ℝ)^k*x^n) ≤ a*((k.factorial : ℝ)/(1-x)^(k+1)) :=
      mul_le_mul_of_nonneg_left (geometric_power_sum_le x hx hx1 k hk) ha
    _ = (a/(1-x))*(k.factorial : ℝ)*(1/(1-x))^k := by
      rw [pow_succ, div_pow]
      field_simp
      ring
    _ ≤ (3/2 : ℝ)*(k.factorial : ℝ)*(4/(3*s))^k :=
      mul_le_mul (mul_le_mul_of_nonneg_right hmass (Nat.cast_nonneg _))
        (pow_le_pow_left₀ (by positivity) hu k) (by positivity) (by positivity)

/-- NU-AO-BULK-HISTORY: complete normalized moments at all discounts 8γ≤s≤1. -/
theorem complete_depth_moments (gamma s : ℝ) (hg : 0 < gamma)
    (hgs : 8*gamma ≤ s) (hs1 : s ≤ 1) :
    let x := (3 : ℝ)^(-2*s+5*gamma)
    let a := 1-(3 : ℝ)^(-2*s)
    a*(∑' n : ℕ, (n : ℝ)^0*x^n) ≤ 3/2 ∧
    a*(∑' n : ℕ, (n : ℝ)^1*x^n) ≤ 2/s ∧
    a*(∑' n : ℕ, (n : ℝ)^2*x^n) ≤ 16/(3*s^2) ∧
    a*(∑' n : ℕ, (n : ℝ)^3*x^n) ≤ 64/(3*s^3) := by
  let x := (3 : ℝ)^(-2*s+5*gamma)
  let a := 1-(3 : ℝ)^(-2*s)
  have hs : 0 < s := by linarith only [hg,hgs]
  have hx : 0 ≤ x := Real.rpow_nonneg (by norm_num) _
  have hxy : x ≤ (3 : ℝ)^(-(11/8 : ℝ)*s) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith only [hgs]
  have hy1 : (3 : ℝ)^(-(11/8 : ℝ)*s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs])
  have hx1 : x < 1 := hxy.trans_lt hy1
  have ha : 0 ≤ a := by
    have h := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 3)
      (by linarith only [hs] : -2*s ≤ 0)
    exact sub_nonneg.mpr h
  have hgap : (3/4 : ℝ)*s ≤ 1-x :=
    (geometric_denominator s hs.le hs1).trans (sub_le_sub_left hxy 1)
  have hmass : a/(1-x) ≤ 3/2 := by
    apply (div_le_iff₀ (sub_pos.mpr hx1)).mpr
    have h := geometric_normalization s
    have h16 := mul_le_mul_of_nonneg_left (sub_le_sub_left hxy 1) (by norm_num : (0 : ℝ) ≤ 16/11)
    dsimp [a]
    linarith only [h,h16,hx1]
  have h0 := normalized_moment_bound a x s ha hx hx1 hs hmass hgap 0 (by decide)
  have h1 := normalized_moment_bound a x s ha hx hx1 hs hmass hgap 1 (by decide)
  have h2 := normalized_moment_bound a x s ha hx hx1 hs hmass hgap 2 (by decide)
  have h3 := normalized_moment_bound a x s ha hx hx1 hs hmass hgap 3 (by decide)
  change a*(∑' n : ℕ, (n : ℝ)^0*x^n) ≤ 3/2 ∧
    a*(∑' n : ℕ, (n : ℝ)^1*x^n) ≤ 2/s ∧
    a*(∑' n : ℕ, (n : ℝ)^2*x^n) ≤ 16/(3*s^2) ∧
    a*(∑' n : ℕ, (n : ℝ)^3*x^n) ≤ 64/(3*s^3)
  refine ⟨by simpa using h0, ?_, ?_, ?_⟩
  · convert h1 using 1
    norm_num
    field_simp
    ring
  · convert h2 using 1
    norm_num
    field_simp
    ring
  · convert h3 using 1
    norm_num
    field_simp
    ring

end ASDExplicitGamma.Numerics.AllOrder
