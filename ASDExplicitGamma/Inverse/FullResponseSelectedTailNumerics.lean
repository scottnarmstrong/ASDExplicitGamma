module

public import ASDExplicitGamma.Inverse.FullResponseTraceLp
public import ASDExplicitGamma.Numerics.Inverse.RealBounds
public import Mathlib.Analysis.MeanInequalitiesPow

/-! Genuine real tail estimates for the two finite full-response orders. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- The first full-row tail argument is exactly the source 3^57/32. -/
theorem full_response_first_tail_argument :
    heightExponent (377+11)/32=(3^57/32:ℝ) := by
  norm_num [heightExponent,Real.rpow_natCast]

/-- A uniform selected-wave tail cap on the closed interval containing
both certified orders. A positive Taylor term proves the real exponential bound. -/
theorem full_response_wave_tail_tiny (γ p : ℝ) (hg : γ ≤ gammaZero)
    (hp : 64 ≤ p) (hp128 : p ≤ 128) :
    40*(4*p+2)*selectedWaveTailBudget γ p 377 0 ≤ (1/10^100:ℝ) := by
  have hp0 : 0 < p := by linarith only [hp]
  have hclock : (3:ℝ)^(4*γ*351) ≤ 3 := by
    have he : 4*γ*351 ≤ 1 := by change γ ≤ 17/50000 at hg; linarith only [hg]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) he
  have hexp : (selectedTailProbability 377 0)^(1/(2*p):ℝ) =
      Real.exp (-(3^57/32:ℝ)/(2*p)) := by
    rw [selected_wave_tail_probability,full_response_first_tail_argument]
    simp only [pow_zero,mul_one]
    congr 1
    ring
  have hden : (3^57/32:ℝ)/256 ≤ (3^57/32:ℝ)/(2*p) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [hp128])
  have ht := inv_exp_neg_factorial_bound ((3^57/32:ℝ)/256) (by norm_num) 8
  have he := (Real.exp_le_exp.mpr (neg_le_neg hden)).trans ht
  rw [← neg_div] at he
  have hcoef : 40*(4*p+2)*(1000/999:ℝ) ≤ 41120 := by
    nlinarith only [hp,hp128]
  unfold selectedWaveTailBudget
  simp only [Fin.val_zero,pow_zero,mul_one,selectedFirstClock]
  norm_num only [Nat.cast_ofNat]
  rw [hexp]
  have hc0 : 0 ≤ 40*(4*p+2)*(1000/999:ℝ) := by positivity
  calc
    _ = (40*(4*p+2)*(1000/999:ℝ))*((3:ℝ)^(4*γ*351))*
        Real.exp (-(3^57/32:ℝ)/(2*p)) := by ring
    _ ≤ (41120:ℝ)*3*((Nat.factorial 8:ℝ)/((3^57/32:ℝ)/256)^8) := by
      exact mul_le_mul (mul_le_mul hcoef hclock (by positivity) (by norm_num)) he
        (Real.exp_pos _).le (by norm_num)
    _ ≤ _ := by norm_num

/-- The j=1 wave tail is exactly the first clock 351 times the j=0 tail. -/
theorem full_response_wave_first_tail_tiny (γ p : ℝ) (hg : γ ≤ gammaZero)
    (hp : 64 ≤ p) (hp128 : p ≤ 128) :
    40*(4*p+2)*selectedWaveTailBudget γ p 377 1 ≤ 351*(1/10^100:ℝ) := by
  have he : selectedWaveTailBudget γ p 377 1=351*selectedWaveTailBudget γ p 377 0 := by
    simp [selectedWaveTailBudget,selectedFirstClock]
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (full_response_wave_tail_tiny γ p hg hp hp128)
    (by norm_num : (0:ℝ) ≤ 351)
  convert hh using 1
  ring

end
end ASDExplicitGamma.Inverse
