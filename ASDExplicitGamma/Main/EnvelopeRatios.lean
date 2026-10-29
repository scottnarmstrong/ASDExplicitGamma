module

public import ASDExplicitGamma.Main.LoadsAndSlopes
public import ASDExplicitGamma.Statements.GammaZero

/-! Positive denominators for the actual main history transport slopes. -/

@[expose] public section

namespace ASDExplicitGamma.Main

/-- The weak-history square is a single real power. -/
theorem mainAlpha_sq : mainAlpha^2 = (3:ℝ)^(-(1/2:ℝ)) := by
  unfold mainAlpha
  rw [← Real.rpow_mul_natCast (by norm_num) _ 2]
  norm_num

/-- A common strict denominator gate covers all main weak-history terms. -/
theorem main_weak_ratio_lt_one (gamma e : ℝ) (hg : gamma ≤ gammaZero)
    (he : e ≤ 10*gamma+1/64) : mainAlpha^2*(3:ℝ)^e < 1 := by
  rw [mainAlpha_sq, ← Real.rpow_add (by norm_num)]
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  norm_num [gammaZero] at hg
  linarith only [he, hg]

theorem mainRawA_nonneg {gamma : ℝ} (hg : 0 ≤ gamma) : 0 ≤ mainRawA gamma := by
  unfold mainRawA
  positivity

theorem mainRawS_nonneg {gamma : ℝ} (hg : 0 ≤ gamma) : 0 ≤ mainRawS gamma := by
  exact mul_nonneg (by norm_num) hg

/-- Positivity uses the genuine raw mean/slope and the genuine geometric denominator. -/
theorem mainRawGeo_nonneg {gamma q : ℝ} (hg : 0 ≤ gamma) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ mainRawGeo gamma q := by
  have hA := mainRawA_nonneg hg
  have hS := mainRawS_nonneg hg
  unfold mainRawGeo
  exact add_nonneg (div_nonneg hA (sub_pos.mpr hq1).le)
    (div_nonneg (mul_nonneg hS hq) (sq_nonneg _))

theorem mainW_nonneg {gamma r : ℝ} (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (hr : r ≤ 10) (n : ℕ) : 0 ≤ mainW gamma r n := by
  have hnum : 0 ≤ 1-mainAlpha^2 := by
    have h := main_weak_ratio_lt_one gamma 0 hg (by linarith only [hg0])
    simpa only [Real.rpow_zero, mul_one] using (sub_pos.mpr h).le
  have hpow := main_weak_ratio_lt_one gamma (r*gamma-n) hg (by
    have h := mul_le_mul_of_nonneg_right hr hg0
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith only [h, hn])
  exact div_nonneg hnum (sub_pos.mpr hpow).le

theorem mainRawW_nonneg {gamma r : ℝ} (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (hr : r ≤ 10) (n : ℕ) : 0 ≤ mainRawW gamma r n := by
  have hnum : 0 ≤ 1-mainAlpha^2 := by
    have h := main_weak_ratio_lt_one gamma 0 hg (by linarith only [hg0])
    simpa only [Real.rpow_zero, mul_one] using (sub_pos.mpr h).le
  have hpow := main_weak_ratio_lt_one gamma (r*gamma-n) hg (by
    have h := mul_le_mul_of_nonneg_right hr hg0
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith only [h, hn])
  exact mul_nonneg hnum (mainRawGeo_nonneg hg0 (by positivity) hpow)

end ASDExplicitGamma.Main
