module

public import ASDExplicitGamma.Native.HeatMomentUniformBound
public import ASDExplicitGamma.Numerics.Native.HeatSoundness

/-! Exact rational heat coefficients enclose the analytical moment transition. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native
noncomputable section

/-- Every degree of the source's rounded binomial row encloses its analytical
transition entry, using the existing certified exponential enclosure. -/
theorem heat_moment_transition_le_rounded_coefficient (c ee : ℚ) (hc : 0 ≤ c)
    (hcheck : nativeHeatExpCheck c ee = true) (j : ℕ) (hj : j ≤ 20) :
    heatMomentTransition c 20 j 1 ≤ ((nativeHeatCoefficients ee).getD j 0:ℝ) := by
  have he := nativeHeatExpCheck_sound hcheck
  have hcR : (0:ℝ) ≤ c := by exact_mod_cast hc
  have hi : 0 ≤ Real.exp (c:ℝ)-1 := sub_nonneg.mpr (Real.one_le_exp hcR)
  have he0 : (0:ℝ) ≤ ee := (Real.exp_nonneg _).trans he
  have hpoly := mul_le_mul (pow_le_pow_left₀ (Real.exp_nonneg _) he j)
    (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 4*(Real.exp (c:ℝ)-1))
      (mul_le_mul_of_nonneg_left (sub_le_sub_right he 1) (by norm_num : (0:ℝ)≤4)) (20-j))
    (pow_nonneg (by positivity) _) (pow_nonneg he0 _)
  have hchoose := mul_le_mul_of_nonneg_left hpoly (Nat.cast_nonneg (Nat.choose 20 j))
  have hget : (nativeHeatCoefficients ee).getD j 0 =
      nativeUp ((Nat.choose 20 j:ℚ)*ee^j*(4*(ee-1))^(20-j)) := by
    simp [nativeHeatCoefficients,show j < 21 by omega]
  rw [hget]
  have hup : (((Nat.choose 20 j:ℚ)*ee^j*(4*(ee-1))^(20-j):ℚ):ℝ) ≤
      (nativeUp ((Nat.choose 20 j:ℚ)*ee^j*(4*(ee-1))^(20-j)):ℝ) := by
    exact_mod_cast nativeUp_ge ((Nat.choose 20 j:ℚ)*ee^j*(4*(ee-1))^(20-j))
  apply le_trans _ hup
  simpa only [heatMomentTransition,heatMomentGreenKernel,mul_one,Rat.cast_mul,Rat.cast_pow,
    Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_sub,Rat.cast_one,mul_assoc] using hchoose

end
end ASDExplicitGamma.Native
