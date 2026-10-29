module

public import ASDExplicitGamma.Inverse.WeightedLocalizationRetainedPowers
public import Mathlib.Algebra.Order.Ring.Pow

/-! The exact six-depth localization radius and its infinite-tail improvement. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- Literal retained-label radius N=3^(floor(R/6)+1). -/
def localizationCutoffRadius (R : ℕ) : ℕ := 3 ^ (R / 6 + 1)

/-- The complete post-entrance radius, not a finite scan of residue classes. -/
theorem localization_cutoff_radius_from_sixty (R : ℕ) (hR : 60 ≤ R) :
    localizationCutoffRadius R = 3 ^ 11 * 3 ^ ((R - 60) / 6) := by
  have he : R / 6 + 1 = 11 + (R - 60) / 6 := by omega
  rw [localizationCutoffRadius, he, pow_add]

/-- The exact radius satisfies the source real-power upper envelope. -/
theorem localization_cutoff_radius_le (R : ℕ) :
    (localizationCutoffRadius R : ℝ) ≤ 3 * (3 : ℝ) ^ ((R : ℝ) / 6) := by
  have hn : 6 * (R / 6) ≤ R := by omega
  have hc : (6 : ℝ) * (R / 6 : ℕ) ≤ R := by exact_mod_cast hn
  have he : ((R / 6 : ℕ) : ℝ) ≤ (R : ℝ) / 6 := by linarith only [hc]
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) he
  rw [Real.rpow_natCast] at hp
  unfold localizationCutoffRadius
  push_cast
  rw [pow_succ (3 : ℝ) (R / 6)]
  nlinarith only [hp]

/-- The mismatch exponential improves at every later depth; 3^130 pays the
worst residue in each six-depth block, exactly as in retained PE. -/
theorem localization_mismatch_exponential_decay (p : ℝ) (hp : 0 < p) (hp256 : p ≤ 256)
    (R : ℕ) (hR : 60 ≤ R) :
    Real.exp (-(localizationCutoffRadius R : ℝ) / (6 * p)) ≤
      Real.exp (-(3 : ℝ) ^ 11 / (6 * p)) * (3 : ℝ) ^ (130 - 2 * (R : ℝ)) := by
  let t := (R - 60) / 6
  let A := (3 : ℝ) ^ 11 / (6 * p)
  have hA : 12 ≤ A := by
    apply (le_div_iff₀ (by positivity : 0 < 6 * p)).mpr
    norm_num
    nlinarith only [hp256]
  have hlog : Real.log 3 ≤ 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at hh
    exact hh
  have hc : 12 * Real.log 3 ≤ 2 * A := by linarith only [hA, hlog]
  have hpow : 1 + 2 * (t : ℝ) ≤ (3 : ℝ) ^ t := by
    have hh := one_add_mul_le_pow (a := (2 : ℝ)) (by norm_num) t
    norm_num at hh
    nlinarith only [hh]
  have hterm : (localizationCutoffRadius R : ℝ) / (6 * p) = A * (3 : ℝ) ^ t := by
    rw [localization_cutoff_radius_from_sixty R hR]
    push_cast
    dsimp only [A, t]
    ring
  have he : -(localizationCutoffRadius R : ℝ) / (6 * p) ≤ -A - 12 * (t : ℝ) * Real.log 3 := by
    rw [neg_div, hterm]
    have h1 := mul_le_mul_of_nonneg_left hpow (by linarith only [hA] : 0 ≤ A)
    have h2 := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg t)
    nlinarith only [h1, h2]
  have hex : Real.exp (-A - 12 * (t : ℝ) * Real.log 3) =
      Real.exp (-A) * (3 : ℝ) ^ (-12 * (t : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]
    congr 1
    ring
  have hdepth : (-12 : ℝ) * t ≤ 130 - 2 * (R : ℝ) := by
    have hn : R ≤ 65 + 6 * t := by dsimp only [t]; omega
    have hh : (R : ℝ) ≤ 65 + 6 * (t : ℝ) := by exact_mod_cast hn
    linarith only [hh]
  calc
    _ ≤ Real.exp (-A - 12 * (t : ℝ) * Real.log 3) := Real.exp_le_exp.mpr he
    _ = Real.exp (-A) * (3 : ℝ) ^ (-12 * (t : ℝ)) := hex
    _ ≤ Real.exp (-A) * (3 : ℝ) ^ (130 - 2 * (R : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hdepth) (Real.exp_pos _).le
    _ = _ := by dsimp only [A]; rw [neg_div]

end ASDExplicitGamma.Inverse
