/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import ASDExplicitGamma.AllOrder.SmallGammaSeed
public import ASDExplicitGamma.Inverse.RestrictionReset

/-! # Small-gamma cap extraction from the all-order profiles -/

@[expose] public section

namespace ASDExplicitGamma.AllOrder

private theorem aoCir_height_ratio_le (n : ℕ) :
    (397 + 12 * ((n + 2 : ℕ) : ℝ)) / (3 : ℝ) ^ (n + 1) ≤ 421 / 3 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hnum :
        397 + 12 * ((Nat.succ n + 2 : ℕ) : ℝ) ≤
          3 * (397 + 12 * ((n + 2 : ℕ) : ℝ)) := by
      push_cast
      nlinarith
    calc
      (397 + 12 * ((Nat.succ n + 2 : ℕ) : ℝ)) /
          (3 : ℝ) ^ (Nat.succ n + 1) =
        (397 + 12 * ((Nat.succ n + 2 : ℕ) : ℝ)) /
          ((3 : ℝ) ^ (n + 1) * 3) := by
            rw [show Nat.succ n + 1 = (n + 1) + 1 by omega, pow_succ]
      _ ≤ (3 * (397 + 12 * ((n + 2 : ℕ) : ℝ))) /
          ((3 : ℝ) ^ (n + 1) * 3) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = (397 + 12 * ((n + 2 : ℕ) : ℝ)) / (3 : ℝ) ^ (n + 1) := by
        field_simp
      _ ≤ 421 / 3 := ih

private theorem aoCir_height_ratio_le_band {k : ℕ} (hk : 2 ≤ k) :
    (397 + 12 * (k : ℝ)) / (3 : ℝ) ^ (k - 1) ≤ 421 / 3 := by
  let n := k - 2
  have hn : n + 2 = k := by dsimp [n]; omega
  have hexp : k - 1 = n + 1 := by omega
  have hcast : (k : ℝ) = ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hn.symm
  rw [hcast, hexp]
  simpa only [Nat.cast_add, Nat.cast_ofNat] using aoCir_height_ratio_le n

private theorem aoCir_order_band_lower (q : ℝ) (hq : 0 < q)
    (hk : 2 ≤ Inverse.orderBand q) :
    64 * (3 : ℝ) ^ (Inverse.orderBand q - 1) < q := by
  let k := Inverse.orderBand q
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hmax0 : 0 < max 1 (q / 64) := by
    exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hx0 : 0 ≤ Real.log (max 1 (q / 64)) / Real.log 3 :=
    div_nonneg (Real.log_nonneg (le_max_left 1 (q / 64))) hlog3.le
  have hceil : (k : ℝ) <
      Real.log (max 1 (q / 64)) / Real.log 3 + 1 := by
    dsimp [k, Inverse.orderBand]
    exact Nat.ceil_lt_add_one hx0
  have hdiv : 1 < Real.log (max 1 (q / 64)) / Real.log 3 := by
    have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hlog : Real.log 3 < Real.log (max 1 (q / 64)) := by
    have h := (lt_div_iff₀ hlog3).mp hdiv
    simpa only [one_mul] using h
  have hmaxExp : 3 < Real.exp (Real.log (max 1 (q / 64))) :=
    (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3)).mp hlog
  have hmax : 3 < max 1 (q / 64) := by
    rwa [Real.exp_log hmax0] at hmaxExp
  have hq64 : 1 < q / 64 := by
    by_contra hnot
    have hle : q / 64 ≤ 1 := le_of_not_gt hnot
    rw [max_eq_left hle] at hmax
    norm_num at hmax
  have hmaxEq : max 1 (q / 64) = q / 64 := max_eq_right hq64.le
  have hceilLower : (k : ℝ) - 1 <
      Real.log (max 1 (q / 64)) / Real.log 3 := by linarith
  have hlogProduct : ((k - 1 : ℕ) : ℝ) * Real.log 3 < Real.log (q / 64) := by
    have hkCast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      exact_mod_cast (Nat.cast_sub (by omega : 1 ≤ k))
    have hceilLower' : ((k - 1 : ℕ) : ℝ) <
        Real.log (max 1 (q / 64)) / Real.log 3 := by
      rw [hkCast]
      exact hceilLower
    rw [hmaxEq] at hceilLower'
    have h := (lt_div_iff₀ hlog3).mp hceilLower'
    simpa only [one_mul] using h
  have hpowEq : Real.exp (((k - 1 : ℕ) : ℝ) * Real.log 3) =
      (3 : ℝ) ^ (k - 1) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  have hpow : (3 : ℝ) ^ (k - 1) < q / 64 := by
    calc
      (3 : ℝ) ^ (k - 1) = Real.exp (((k - 1 : ℕ) : ℝ) * Real.log 3) := hpowEq.symm
      _ < Real.exp (Real.log (q / 64)) := Real.exp_lt_exp.mpr hlogProduct
      _ = q / 64 := Real.exp_log (by positivity)
  have hscaled := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 64)).mp hpow
  nlinarith

/-- The small-gamma staircase supplies exactly the order-band conditions
needed to turn the profile into the 50 and 2.2 CIR caps. -/
theorem aoCir_small_gamma_profile_band_bounds {γ q : ℝ}
    (hγ : 0 < γ) (hγsmall : γ ≤ 1 / 327680)
    (hq : 2 ≤ q) (hqP : q ≤ 4 * (smallGammaSeedP γ : ℝ)) :
    γ * ((Inverse.heightEntrance (Inverse.orderBand q) : ℝ) + 20) < 1 / 800 ∧
      γ * q ≤ 1 / 4096 := by
  let x : ℝ := (1 / 16384 : ℝ) / (2 * γ)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx10 : 10 ≤ x := by
    dsimp [x]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * γ)]
    norm_num at hγsmall ⊢
    linarith
  have hfloor10 : 10 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 hx10
  have hfloorDouble : 20 ≤ 2 * ⌊x⌋₊ := by omega
  have hP : smallGammaSeedP γ = 2 * ⌊x⌋₊ := by
    simp only [smallGammaSeedP, x, max_eq_right hfloorDouble]
  have hPcast : (smallGammaSeedP γ : ℝ) = 2 * (⌊x⌋₊ : ℝ) := by
    rw [hP]
    norm_num
  have hPupper : γ * (smallGammaSeedP γ : ℝ) ≤ 1 / 16384 := by
    have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    calc
      γ * (smallGammaSeedP γ : ℝ) = γ * (2 * (⌊x⌋₊ : ℝ)) := by rw [hPcast]
      _ ≤ γ * (2 * x) := mul_le_mul_of_nonneg_left (by linarith) hγ.le
      _ = 1 / 16384 := by
        dsimp [x]
        field_simp [ne_of_gt hγ]
  have horder : γ * q ≤ 1 / 4096 := by
    calc
      γ * q ≤ γ * (4 * (smallGammaSeedP γ : ℝ)) :=
        mul_le_mul_of_nonneg_left hqP hγ.le
      _ = 4 * (γ * (smallGammaSeedP γ : ℝ)) := by ring
      _ ≤ 4 * (1 / 16384) := by nlinarith [hPupper]
      _ = 1 / 4096 := by norm_num
  let k := Inverse.orderBand q
  have hheight : (Inverse.heightEntrance k : ℝ) + 20 = 397 + 12 * (k : ℝ) := by
    norm_num [Inverse.heightEntrance]
    ring
  have hshift : γ * (397 + 12 * (k : ℝ)) < 1 / 800 := by
    by_cases hk : k ≤ 1
    · have hA : 397 + 12 * (k : ℝ) ≤ 409 := by
        have hkR : (k : ℝ) ≤ 1 := by exact_mod_cast hk
        linarith
      calc
        γ * (397 + 12 * (k : ℝ)) ≤ γ * 409 :=
          mul_le_mul_of_nonneg_left hA hγ.le
        _ ≤ 409 / 327680 := by nlinarith [hγsmall]
        _ < 1 / 800 := by norm_num
    · have hk : 2 ≤ k := by omega
      have hband := aoCir_order_band_lower q (by linarith [hq]) hk
      have hgammaBand : γ < (1 / 16384 : ℝ) / (16 * (3 : ℝ) ^ (k - 1)) := by
        have hscaled : γ * (64 * (3 : ℝ) ^ (k - 1)) < 1 / 4096 := by
          calc
            γ * (64 * (3 : ℝ) ^ (k - 1)) < γ * q :=
              mul_lt_mul_of_pos_left hband hγ
            _ ≤ 1 / 4096 := horder
        apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 16 * (3 : ℝ) ^ (k - 1))).2
        nlinarith [hscaled]
      have hratio := aoCir_height_ratio_le_band hk
      have hApos : 0 < 397 + 12 * (k : ℝ) := by positivity
      calc
        γ * (397 + 12 * (k : ℝ)) <
            ((1 / 16384 : ℝ) / (16 * (3 : ℝ) ^ (k - 1))) *
              (397 + 12 * (k : ℝ)) :=
          mul_lt_mul_of_pos_right hgammaBand hApos
        _ = (1 / 16384 : ℝ) / 16 *
            ((397 + 12 * (k : ℝ)) / (3 : ℝ) ^ (k - 1)) := by
          field_simp
        _ ≤ (1 / 16384 : ℝ) / 16 * (421 / 3) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        _ < 1 / 800 := by norm_num
  exact ⟨by rw [hheight]; exact hshift, horder⟩

/-- The fine-grid factor in the small-gamma inverse history cap. -/
theorem aoCir_grid_refinement_factor_lt {q : ℝ} (hq : 48 ≤ q) :
    (3 : ℝ) ^ (8 / q) < 1201 / 1000 := by
  have hq0 : 0 < q := by linarith
  have hexp : 8 / q ≤ (1 / 6 : ℝ) := by
    rw [div_le_iff₀ hq0]
    nlinarith
  have hgrid : (3 : ℝ) ^ (8 / q) ≤ (3 : ℝ) ^ (1 / 6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hrootpow : ((3 : ℝ) ^ (1 / 6 : ℝ)) ^ 6 = 3 := by
    have h := Real.rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 3)
      (by norm_num : 6 ≠ 0)
    norm_num at h
    exact h
  have hroot : (3 : ℝ) ^ (1 / 6 : ℝ) < 1201 / 1000 :=
    lt_of_pow_lt_pow_left₀ 6 (by positivity)
      (by rw [hrootpow]; norm_num)
  exact hgrid.trans_lt hroot

/-- A real exponential over the profile exponent is bounded by the
two-sided Padé majorant used for the rational cap checks. -/
private theorem aoCir_three_rpow_le_pade {e x : ℝ}
    (he : 0 ≤ e) (hex : (11 / 10 : ℝ) * e ≤ x)
    (hx0 : 0 ≤ x) (hx2 : x < 2) :
    (3 : ℝ) ^ e ≤ (2 + x) / (2 - x) := by
  have hlog : Real.log 3 ≤ (11 / 10 : ℝ) := by
    have h := Real.log_three_lt_d9
    norm_num at h ⊢
    linarith
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  calc
    Real.exp (Real.log 3 * e) ≤ Real.exp ((11 / 10 : ℝ) * e) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hlog he
    _ ≤ Real.exp x := Real.exp_le_exp.mpr hex
    _ ≤ (2 + x) / (2 - x) := Real.exp_le_two_add_div_two_sub hx0 hx2

/-- The complete inverse-history multiplier at physical exponent `γ`. -/
noncomputable def aoCirInverseHistoryFactor (γ : ℝ) : ℝ :=
  (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ))) /
    (1 - (3 : ℝ) ^ (-(5 / 24 : ℝ) + 2 * γ))

/-- The history factor is increasing in the physical exponent and is
strictly below 1.178 throughout the source range `0 ≤ γ ≤ γ₀`. -/
theorem aoCir_inverse_history_factor_cap {γ : ℝ}
    (hγ0 : γ ≤ 17 / 50000) :
    0 ≤ aoCirInverseHistoryFactor γ ∧ aoCirInverseHistoryFactor γ < 1178 / 1000 := by
  have hquarterpow : ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ 4 = 1 / 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hquarterLo : 759835 / 1000000 < (3 : ℝ) ^ (-(1 / 4 : ℝ)) :=
    lt_of_pow_lt_pow_left₀ 4 (by positivity)
      (by rw [hquarterpow]; norm_num)
  have hquarterHi : (3 : ℝ) ^ (-(1 / 4 : ℝ)) < 760 / 1000 :=
    lt_of_pow_lt_pow_left₀ 4 (by positivity)
      (by rw [hquarterpow]; norm_num)
  have hbasePow : ((3 : ℝ) ^ (-(5 / 24 : ℝ))) ^ 24 = 1 / 243 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hbase : (3 : ℝ) ^ (-(5 / 24 : ℝ)) < 7955 / 10000 :=
    lt_of_pow_lt_pow_left₀ 24 (by positivity)
      (by rw [hbasePow]; norm_num)
  let δ : ℝ := 17 / 25000
  let x : ℝ := (11 / 10 : ℝ) * δ
  have hδ0 : 0 ≤ δ := by norm_num [δ]
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx2 : x < 2 := by norm_num [x, δ]
  have hdeltaPow : (3 : ℝ) ^ δ ≤ (2 + x) / (2 - x) :=
    aoCir_three_rpow_le_pade hδ0 (by dsimp [x]; rfl) hx0 hx2
  have hdelta : (3 : ℝ) ^ δ < 100075 / 100000 := by
    exact hdeltaPow.trans_lt (by norm_num [x, δ])
  have hendpoint :
      (3 : ℝ) ^ (-(5 / 24 : ℝ) + 17 / 25000) < 7961 / 10000 := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    calc
      (3 : ℝ) ^ (-(5 / 24 : ℝ)) * (3 : ℝ) ^ (17 / 25000) ≤
          (7955 / 10000 : ℝ) * (3 : ℝ) ^ (17 / 25000) :=
        mul_le_mul_of_nonneg_right hbase.le (Real.rpow_nonneg (by norm_num) _)
      _ < (7955 / 10000 : ℝ) * (100075 / 100000) :=
        mul_lt_mul_of_pos_left hdelta (by norm_num)
      _ < 7961 / 10000 := by norm_num
  have hexp : -(5 / 24 : ℝ) + 2 * γ ≤ -(5 / 24 : ℝ) + 17 / 25000 := by
    norm_num at hγ0 ⊢
    linarith
  have hdenPow : (3 : ℝ) ^ (-(5 / 24 : ℝ) + 2 * γ) ≤
      (3 : ℝ) ^ (-(5 / 24 : ℝ) + 17 / 25000) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hdenPowLt : (3 : ℝ) ^ (-(5 / 24 : ℝ) + 2 * γ) < 7961 / 10000 :=
    hdenPow.trans_lt hendpoint
  have hnumPos : 0 < 1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by
    nlinarith
  have hdenPos : 0 < 1 - (3 : ℝ) ^ (-(5 / 24 : ℝ) + 2 * γ) := by
    linarith
  have hratio : aoCirInverseHistoryFactor γ ≤
      (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ))) /
        (1 - (3 : ℝ) ^ (-(5 / 24 : ℝ) + 17 / 25000)) := by
    unfold aoCirInverseHistoryFactor
    apply div_le_div_of_nonneg_left hnumPos.le
      (by linarith [hendpoint])
    linarith
  have hratioUpper :
      (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ))) /
        (1 - (3 : ℝ) ^ (-(5 / 24 : ℝ) + 17 / 25000)) < 1178 / 1000 := by
    apply (div_lt_iff₀ (by linarith [hendpoint])).2
    nlinarith [hquarterLo, hendpoint]
  constructor
  · exact div_nonneg hnumPos.le hdenPos.le
  · exact hratio.trans_lt hratioUpper

/-- The trace profile gives the source small-gamma trace cap on the
eight-shell band. `hshift` and `horder` are the order-band bounds established
in the source profile assembly. -/
theorem aoCir_small_gamma_trace_profile_cap
    {γ h p D f T : ℝ}
    (hγ : 0 ≤ γ) (hh : 0 ≤ h) (hγsmall : γ ≤ 1 / 327680)
    (hp : 0 ≤ p) (hD0 : 0 ≤ D) (hD : D ≤ 9)
    (hf0 : 0 ≤ f) (hf : f ≤ 1)
    (hshift : γ * (h + 20) ≤ 1 / 800)
    (horder : γ * p ≤ 1 / 4096)
    (hprofile : T ≤ 4 * (2 + 2810 * γ * (h + 20 + p * (D + 1))) *
      (3 : ℝ) ^ (4 * γ * (h + 20) + 2 * γ * D + 2 * γ * f)) :
    T < 50 := by
  have hamp : γ * (h + 20 + p * (D + 1)) ≤
      1 / 800 + 10 / 4096 := by
    have hDplus : D + 1 ≤ 10 := by linarith
    have hprod : γ * p * (D + 1) ≤ 10 / 4096 := by
      calc
        γ * p * (D + 1) ≤ γ * p * 10 :=
          mul_le_mul_of_nonneg_left hDplus (mul_nonneg hγ hp)
        _ ≤ 10 / 4096 := by nlinarith [horder]
    calc
      γ * (h + 20 + p * (D + 1)) = γ * (h + 20) + γ * p * (D + 1) := by ring
      _ ≤ 1 / 800 + 10 / 4096 := add_le_add hshift hprod
  have hexp : 4 * γ * (h + 20) + 2 * γ * D + 2 * γ * f ≤
      4 / 800 + 20 / 327680 := by
    have hDterm : 2 * γ * D ≤ 18 * γ := by
      nlinarith [mul_le_mul_of_nonneg_left hD hγ]
    have hfterm : 2 * γ * f ≤ 2 * γ := by
      nlinarith [mul_le_mul_of_nonneg_left hf hγ]
    calc
      _ ≤ 4 / 800 + 18 * γ + 2 * γ := by nlinarith [hshift, hDterm, hfterm]
      _ ≤ 4 / 800 + 20 / 327680 := by nlinarith [hγsmall]
  have he0 : 0 ≤ 4 * γ * (h + 20) + 2 * γ * D + 2 * γ * f := by positivity
  let x : ℝ := (4 / 800 + 20 / 327680) * (11 / 10)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx2 : x < 2 := by norm_num [x]
  have hpow : (3 : ℝ) ^ (4 * γ * (h + 20) + 2 * γ * D + 2 * γ * f) ≤
      (2 + x) / (2 - x) := by
    apply aoCir_three_rpow_le_pade he0
    · dsimp [x]
      calc
        (11 / 10 : ℝ) *
            (4 * γ * (h + 20) + 2 * γ * D + 2 * γ * f) ≤
          (11 / 10 : ℝ) * (4 / 800 + 20 / 327680) :=
            mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 11 / 10)
        _ = x := by dsimp [x]; ring
    · exact hx0
    · exact hx2
  have hcoeff :
      4 * (2 + 2810 * γ * (h + 20 + p * (D + 1))) ≤
        4 * (2 + 2810 * (1 / 800 + 10 / 4096 : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_left hamp (by norm_num : (0 : ℝ) ≤ 2810)
    nlinarith [hm]
  have hcoeff0 : 0 ≤ 4 * (2 + 2810 * γ * (h + 20 + p * (D + 1))) := by
    positivity
  have hcoeffUpper0 : 0 ≤ 4 * (2 + 2810 * (1 / 800 + 10 / 4096 : ℝ)) := by
    positivity
  calc
    T ≤ 4 * (2 + 2810 * γ * (h + 20 + p * (D + 1))) *
        (3 : ℝ) ^ (4 * γ * (h + 20) + 2 * γ * D + 2 * γ * f) := hprofile
    _ ≤ 4 * (2 + 2810 * (1 / 800 + 10 / 4096 : ℝ)) *
        (3 : ℝ) ^ (4 * γ * (h + 20) + 2 * γ * D + 2 * γ * f) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (by norm_num) _)
    _ ≤ 4 * (2 + 2810 * (1 / 800 + 10 / 4096 : ℝ)) * ((2 + x) / (2 - x)) :=
      mul_le_mul_of_nonneg_left hpow hcoeffUpper0
    _ < 50 := by norm_num [x]

/-- The inverse-root profile, after the complete-history and four-level
fine-grid factors, gives the source 2.2 cap used by the small-gamma CIR step.
The history factor is derived internally from its source formula. -/
theorem aoCir_small_gamma_inverse_profile_cap
    {γ h f q R : ℝ}
    (hγ : 0 ≤ γ) (hh : 0 ≤ h) (hγsmall : γ ≤ 1 / 327680)
    (hshift : γ * (h + 20) ≤ 1 / 800)
    (hf0 : 0 ≤ f) (hf : f ≤ 5)
    (hq : 48 ≤ q)
    (hprofile : R ≤ (153 / 100 : ℝ) *
      (3 : ℝ) ^ (2 * γ * (h + 20) + 2 * γ * f)) :
    aoCirInverseHistoryFactor γ * (3 : ℝ) ^ (8 / q) * R < 2.2 := by
  have hγ0 : γ ≤ 17 / 50000 := by norm_num at hγsmall ⊢; linarith
  have hhistory := aoCir_inverse_history_factor_cap hγ0
  have hexp : 2 * γ * (h + 20) + 2 * γ * f ≤
      2 / 800 + 10 / 327680 := by
    have hfterm : 2 * γ * f ≤ 10 * γ := by
      nlinarith [mul_le_mul_of_nonneg_left hf hγ]
    calc
      _ ≤ 2 / 800 + 10 * γ := by nlinarith [hshift, hfterm]
      _ ≤ 2 / 800 + 10 / 327680 := by nlinarith [hγsmall]
  have he0 : 0 ≤ 2 * γ * (h + 20) + 2 * γ * f := by positivity
  let x : ℝ := (2 / 800 + 10 / 327680) * (11 / 10)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx2 : x < 2 := by norm_num [x]
  have hpow : (3 : ℝ) ^ (2 * γ * (h + 20) + 2 * γ * f) ≤
      (2 + x) / (2 - x) := by
    apply aoCir_three_rpow_le_pade he0
    · dsimp [x]
      calc
        (11 / 10 : ℝ) * (2 * γ * (h + 20) + 2 * γ * f) ≤
          (11 / 10 : ℝ) * (2 / 800 + 10 / 327680) :=
            mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 11 / 10)
        _ = x := by dsimp [x]; ring
    · exact hx0
    · exact hx2
  have hgrid := aoCir_grid_refinement_factor_lt hq
  have hgrid0 : 0 ≤ (3 : ℝ) ^ (8 / q) := Real.rpow_nonneg (by norm_num) _
  have hfactor : aoCirInverseHistoryFactor γ * (3 : ℝ) ^ (8 / q) ≤
      (1178 / 1000) * (1201 / 1000) :=
    mul_le_mul hhistory.2.le hgrid.le hgrid0 (by norm_num)
  have hfactor0 : 0 ≤ aoCirInverseHistoryFactor γ * (3 : ℝ) ^ (8 / q) :=
    mul_nonneg hhistory.1 hgrid0
  have hprofileUpper : R ≤ (153 / 100 : ℝ) * ((2 + x) / (2 - x)) := by
    calc
      R ≤ (153 / 100 : ℝ) *
          (3 : ℝ) ^ (2 * γ * (h + 20) + 2 * γ * f) := hprofile
      _ ≤ (153 / 100 : ℝ) * ((2 + x) / (2 - x)) :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
  calc
    aoCirInverseHistoryFactor γ * (3 : ℝ) ^ (8 / q) * R ≤
        ((1178 / 1000) * (1201 / 1000)) *
          ((153 / 100 : ℝ) * ((2 + x) / (2 - x))) := by
      calc
        _ ≤ (aoCirInverseHistoryFactor γ * (3 : ℝ) ^ (8 / q)) *
            ((153 / 100 : ℝ) * ((2 + x) / (2 - x))) :=
          mul_le_mul_of_nonneg_left hprofileUpper hfactor0
        _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ < 2.2 := by norm_num [x]

/-- The trace profile remains below the source cap 3120 when the terminal
depth is allowed to vary, provided the order-depth product stays in the
direct P12 window. -/
theorem aoCir_depth_trace_profile_cap
    {γ h p D f T : ℝ}
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 17 / 50000)
    (hh : 0 ≤ h) (hp : 2 ≤ p)
    (hD0 : 0 ≤ D) (hDgate : γ * p * (D + 1) ≤ 1 / 256)
    (hf0 : 0 ≤ f) (hf : f ≤ 1)
    (hshift : γ * (h + 20) ≤ 27 / 200)
    (hprofile : T ≤ 4 * (2 + 2810 * γ * (h + 20 + p * (D + 1))) *
      (3 : ℝ) ^ (4 * γ * (h + 20) + 2 * γ * D + 2 * γ * f)) :
    T < 3120 := by
  have hgammaD : γ * D ≤ 1 / 512 := by
    have hpD0 : 2 * D ≤ p * (D + 1) := by nlinarith [hD0, hp]
    have hpD := mul_le_mul_of_nonneg_left hpD0 hγ
    nlinarith [hpD, hDgate]
  have hexp : 4 * γ * (h + 20) + 2 * γ * D + 2 * γ * f ≤ 11 / 20 := by
    have hfγ : 2 * γ * f ≤ 2 * (17 / 50000 : ℝ) := by
      have hfg := mul_le_mul_of_nonneg_left hf hγ
      nlinarith [hfg, hγmax]
    nlinarith [hgammaD, hshift, hfγ, hγmax]
  have hprod : γ * (h + 20 + p * (D + 1)) ≤ 27 / 200 + 1 / 256 := by
    calc
      γ * (h + 20 + p * (D + 1)) = γ * (h + 20) + γ * p * (D + 1) := by ring
      _ ≤ 27 / 200 + 1 / 256 := add_le_add hshift hDgate
  have hcoeff :
      4 * (2 + 2810 * γ * (h + 20 + p * (D + 1))) ≤
        4 * (2 + 2810 * (27 / 200 + 1 / 256 : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2810)]
  have hcoeff0 : 0 ≤ 4 * (2 + 2810 * (27 / 200 + 1 / 256 : ℝ)) := by positivity
  let x : ℝ := (11 / 10 : ℝ) * (11 / 20)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx2 : x < 2 := by norm_num [x]
  have he0 : 0 ≤ 4 * γ * (h + 20) + 2 * γ * D + 2 * γ * f := by positivity
  have hpow : (3 : ℝ) ^ (4 * γ * (h + 20) + 2 * γ * D + 2 * γ * f) ≤
      (2 + x) / (2 - x) := by
    apply aoCir_three_rpow_le_pade he0
    · dsimp [x]
      exact mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ 11 / 10)
    · exact hx0
    · exact hx2
  calc
    T ≤ 4 * (2 + 2810 * γ * (h + 20 + p * (D + 1))) *
        (3 : ℝ) ^ (4 * γ * (h + 20) + 2 * γ * D + 2 * γ * f) := hprofile
    _ ≤ 4 * (2 + 2810 * (27 / 200 + 1 / 256 : ℝ)) *
        (3 : ℝ) ^ (4 * γ * (h + 20) + 2 * γ * D + 2 * γ * f) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (by norm_num) _)
    _ ≤ 4 * (2 + 2810 * (27 / 200 + 1 / 256 : ℝ)) * ((2 + x) / (2 - x)) :=
      mul_le_mul_of_nonneg_left hpow hcoeff0
    _ < 3120 := by norm_num [x]

end ASDExplicitGamma.AllOrder
