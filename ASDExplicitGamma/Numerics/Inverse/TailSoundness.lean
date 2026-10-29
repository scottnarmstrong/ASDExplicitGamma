module
public import ASDExplicitGamma.Numerics.Inverse.SelectedTails
import Mathlib.Tactic.NormNum

/-! Real exponential soundness of both exact 512-factorial tail certificates. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Inverse

theorem inv_physical_tail_bound {x y : ℚ} (hx : 0 < x) (hy : 0 ≤ y) (hdom : y/1024 < 1) :
    (1000/999 : ℝ)*Real.exp (y : ℝ)*Real.exp (-(x : ℝ)) ≤
      ((1000/999*invE (y/1024)^1024*(Nat.factorial 512)/x^512 : ℚ) : ℝ) := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hyR : (0 : ℝ) ≤ y := by exact_mod_cast hy
  have hdR : (y : ℝ)/1024 < 1 := by exact_mod_cast hdom
  have hp := inv_exp_physical_bound hyR hdR
  have ht := inv_exp_neg_factorial_bound (x : ℝ) hxR 512
  calc
    (1000/999 : ℝ)*Real.exp (y : ℝ)*Real.exp (-(x : ℝ)) ≤
        (1000/999 : ℝ)*(1-(y : ℝ)/1024)⁻¹^1024*((Nat.factorial 512 : ℝ)/(x : ℝ)^512) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by norm_num)) ht
        (Real.exp_pos _).le (by positivity)
    _ = _ := by
      unfold invE
      push_cast
      simp only [one_div]
      ring

theorem inv_global_real_tail :
    (1000/999 : ℝ)*Real.exp ((11/10)*512*(17/50000)*307)*
      Real.exp (-(3^46/32 : ℝ)) < (1/10^30 : ℝ)^256 := by
  have h := inv_physical_tail_bound (x := 3^46/32) (y := (11/10)*512*invGamma*307)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have he : ((1000/999*invE (((11/10)*512*invGamma*307)/1024)^1024*
      (Nat.factorial 512)/(3^46/32)^512 : ℚ) : ℝ) = (invGlobalTail : ℝ) := rfl
  rw [he] at h
  have hnum := (Rat.cast_lt (K := ℝ)).2 invGlobal_tail
  norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hnum
  convert h.trans_lt hnum using 1 <;> norm_num [invGamma]

theorem inv_local_real_tail :
    (1000/999 : ℝ)*Real.exp ((11/10)*512*(17/50000)*351)*
      Real.exp (-(3^57/32 : ℝ)) < (1/10^40 : ℝ)^256 := by
  have h := inv_physical_tail_bound (x := 3^57/32) (y := (11/10)*512*invGamma*351)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have he : ((1000/999*invE (((11/10)*512*invGamma*351)/1024)^1024*
      (Nat.factorial 512)/(3^57/32)^512 : ℚ) : ℝ) = (invLocalTail : ℝ) := rfl
  rw [he] at h
  have hnum := (Rat.cast_lt (K := ℝ)).2 invLocal_tail
  norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hnum
  convert h.trans_lt hnum using 1 <;> norm_num [invGamma]

end ASDExplicitGamma.Numerics.Inverse
