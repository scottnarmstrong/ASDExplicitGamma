module

public import ASDExplicitGamma.Inverse.StoppedRareMomentKernel
public import ASDExplicitGamma.Numerics.Inverse.RealBounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! Real soundness of the exact source rare-moment cutoffs and polynomial caps. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Numerics.Inverse
noncomputable section

/-- A checked rational cutoff comparison gives the physical exponential
inequality, using a proved lower bound for exp(1). -/
theorem rare_moment_cutoff_real (q : ℚ) (n : ℕ) (hq : 0 < (q:ℝ))
    (hcut : (200/(26*q):ℚ) ≤ (2718/1000:ℚ)^n) :
    200*Real.exp (-(n:ℝ)) ≤ 26*(q:ℝ) := by
  have hr' := (Rat.cast_le (K := ℝ)).mpr hcut
  have hr : 200/(26*(q:ℝ)) ≤ (2718/1000:ℝ)^n := by
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow] using! hr'
  have he : (2718/1000:ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2718/1000) he n
  rw [← Real.exp_nat_mul,mul_one] at hp
  rw [Real.exp_neg,mul_inv_le_iff₀ (Real.exp_pos _)]
  have hh := (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ) < 26) hq)).mp (hr.trans hp)
  simpa only [mul_comm] using! hh

theorem inverse_moment_polynomials :
    (26*(invInverseQ:ℝ))*rareMomentPolynomial 2 600 = (invInverseM2:ℝ) ∧
    (26*(invInverseQ:ℝ))*rareMomentPolynomial 4 600 = (invInverseM4:ℝ) := by
  norm_num [rareMomentPolynomial,invInverseQ,invInverseM2,invInverseM4]

theorem full_moment_polynomials :
    (26*(invFullQ:ℝ))*rareMomentPolynomial 2 1232 = (invFullM2:ℝ) ∧
    (26*(invFullQ:ℝ))*rareMomentPolynomial 4 1232 = (invFullM4:ℝ) := by
  norm_num [rareMomentPolynomial,invFullQ,invFullM2,invFullM4]

/-- A conservative fixed cutoff suffices for the uniform planar Bernstein
moments at q<=10^-10, independently of the smaller producer-specific q. -/
theorem uniform_rare_moment_cutoff :
    200*Real.exp (-(104:ℝ)/4) ≤ (26/10000000000:ℝ) := by
  have hh := rare_moment_cutoff_real (1/10000000000) 26 (by norm_num) (by norm_num)
  convert hh using 1 <;> norm_num

theorem uniform_rare_moment_caps :
    (26/10000000000:ℝ)*rareMomentPolynomial 4 104 < 8 ∧
    (26/10000000000:ℝ)*rareMomentPolynomial 8 104 < 1000000000 := by
  norm_num [rareMomentPolynomial]

end
end ASDExplicitGamma.Inverse
