module

public import ASDExplicitGamma.Inverse.FixedSelectedHeight

/-! Exact fixed-row density cutoff and floor inputs, discharged from the
rational certificates and the real exponential lower bound. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
open ASDExplicitGamma.Numerics.Inverse

private theorem cutoff_of_rational_power (q : ℝ) (hq : 0 < q) (n : ℕ)
    (hn : 200/(26*q) < (2718/1000:ℝ)^n) :
    200*Real.exp (-(n:ℝ)) ≤ 26*q := by
  have hpow : (2718/1000:ℝ)^n ≤ Real.exp (n:ℝ) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2718/1000) invEuler_real.le n
    simpa only [← Real.exp_nat_mul,Nat.cast_mul,mul_one] using hh
  have hh := (div_le_iff₀ (by positivity : 0 < 26*q)).mp (hn.le.trans hpow)
  rw [Real.exp_neg,← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _)]
  simpa only [mul_comm] using hh

private theorem cutoff_cast (q : ℚ) (n : ℕ)
    (hc : 200/(26*q) < (2718/1000:ℚ)^n) :
    200/(26*(q:ℝ)) < (2718/1000:ℝ)^n := by
  have hh := (Rat.cast_lt (K := ℝ)).mpr hc
  push_cast at hh
  exact hh

/-- Every fixed row supplies the complete density input tuple, with the
actual source cutoffs 600 and 1232 and their respective q floors. -/
theorem root_row_density_parameters (r : RootRow) :
    333 ≤ rootH0 r ∧ 0 < rootTau r ∧ Real.exp (-6000) ≤ rootQ r ∧
      0 ≤ rootMomentCutoff r ∧ 200*Real.exp (-rootMomentCutoff r/4) ≤ 26*rootQ r := by
  have hi : 200*Real.exp (-(600:ℝ)/4) ≤ 26*(invInverseQ:ℝ) := by
    have hq : 0 < (invInverseQ:ℝ) := (Real.exp_pos _).trans inv_inverse_density_floor
    have hc : 200/(26*(invInverseQ:ℝ)) < (2718/1000:ℝ)^150 := by
      exact cutoff_cast _ _ invInverse_cutoff.2
    simpa only [Nat.cast_ofNat,show -(600:ℝ)/4= -(150:ℝ) by norm_num] using cutoff_of_rational_power _ hq 150 hc
  have hf : 200*Real.exp (-(1232:ℝ)/4) ≤ 26*(invFullQ:ℝ) := by
    have hq : 0 < (invFullQ:ℝ) := (Real.exp_pos _).trans inv_full_density_floor
    have hc : 200/(26*(invFullQ:ℝ)) < (2718/1000:ℝ)^308 := by
      exact cutoff_cast _ _ invFull_cutoff.2
    simpa only [Nat.cast_ofNat,show -(1232:ℝ)/4= -(308:ℝ) by norm_num] using cutoff_of_rational_power _ hq 308 hc
  cases r <;> exact ⟨by norm_num [rootH0],by norm_num [rootTau],
    by first | exact inv_inverse_density_floor.le | exact inv_full_density_floor.le,
    by norm_num [rootMomentCutoff],by first | exact hi | exact hf⟩

end ASDExplicitGamma.Inverse
