/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.PerDepth
public import ASDExplicitGamma.AllOrder.HistorySum
public import ASDExplicitGamma.AllOrder.ProfileResetAdapter
public import ASDExplicitGamma.Numerics.Enclosures

/-! Source-level assembly of the real-order all-order depth profile. -/

@[expose] public section

open MeasureTheory Homogenization Algsuperdiff.Section3
open Homogenization.Book
open Homogenization.Book
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

private noncomputable def aoPerDepthRawBound (γ R : ℝ) (t : ℕ) : ℝ :=
  Real.rpow 9 ((t : ℝ) / R) *
    (16 + 22480 * γ * R * ((t : ℝ) + 22)) *
    R ^ (64 * γ) * (3 : ℝ) ^ (4 * γ * ((t : ℝ) + 1))

private theorem aoPerDepth_eLp_ofReal_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : Ω → ℝ) (q A : ℝ)
    (hmem : MemLp f (ENNReal.ofReal q) μ)
    (hnonneg : ∀ x, 0 ≤ f x)
    (hlp : lpNorm f (ENNReal.ofReal q) μ ≤ A) :
    eLpNorm (fun x => ENNReal.ofReal (f x)) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal A := by
  have hEq : eLpNorm f (ENNReal.ofReal q) μ =
      ENNReal.ofReal (lpNorm f (ENNReal.ofReal q) μ) := by
    have htoReal : (eLpNorm f (ENNReal.ofReal q) μ).toReal =
        lpNorm f (ENNReal.ofReal q) μ := toReal_eLpNorm
    rw [← htoReal]
    exact (ENNReal.ofReal_toReal hmem.eLpNorm_ne_top).symm
  change eLpNorm (ENNReal.ofReal ∘ f) (ENNReal.ofReal q) μ ≤ _
  rw [eLpNorm_ofReal _ (Filter.Eventually.of_forall hnonneg), hEq]
  exact ENNReal.ofReal_le_ofReal hlp

private theorem aoPerDepth_ofReal_product_le {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a * b ≤ c) :
    ENNReal.ofReal a * ENNReal.ofReal b ≤ ENNReal.ofReal c := by
  calc
    _ = ENNReal.ofReal (a * b) := (ENNReal.ofReal_mul ha).symm
    _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal hab

private theorem aoPerDepth_population_le {q : ℝ} {t : ℕ}
    (hq : 4 + 3 * (t : ℝ) ≤ q) :
    Real.rpow 9 ((t : ℝ) / q) ≤ 21 / 10 := by
  have hqpos : 0 < q := by linarith [hq]
  have hexp : (t : ℝ) / q ≤ 1 / 3 := by
    apply (div_le_iff₀ hqpos).2
    nlinarith [hq]
  have hmono := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 9) hexp
  have hcube : (Real.rpow 9 (1 / 3 : ℝ)) ^ 3 = 9 := by
    have h := Real.rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 9)
      (by norm_num : 3 ≠ 0)
    convert h using 1 <;> norm_num
  have hroot : Real.rpow 9 (1 / 3 : ℝ) < 21 / 10 := by
    apply lt_of_pow_lt_pow_left₀ 3 (by positivity)
    calc
      (Real.rpow 9 (1 / 3 : ℝ)) ^ 3 = 9 := hcube
      _ < (21 / 10 : ℝ) ^ 3 := by norm_num
  exact hmono.trans hroot.le

private theorem aoPerDepth_population_two_le {t : ℕ} (ht : t ≤ 5) :
    Real.rpow 9 ((t : ℝ) / 20) ≤ 2 := by
  have hexp : (t : ℝ) / 20 ≤ 1 / 4 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 20)).2
    norm_num
    exact_mod_cast ht
  have hmono := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 9) hexp
  have hfourth : (Real.rpow 9 (1 / 4 : ℝ)) ^ 4 = 9 := by
    have h := Real.rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 9)
      (by norm_num : 4 ≠ 0)
    convert h using 1 <;> norm_num
  have hroot : Real.rpow 9 (1 / 4 : ℝ) < 2 := by
    apply lt_of_pow_lt_pow_left₀ 4 (by norm_num)
    calc
      (Real.rpow 9 (1 / 4 : ℝ)) ^ 4 = 9 := hfourth
      _ < (2 : ℝ) ^ 4 := by norm_num
  exact hmono.trans hroot.le

private theorem aoPerDepth_twenty_power_le {γ : ℝ}
    (hγ : γ ≤ 17 / 50000) :
    (20 : ℝ) ^ (64 * γ) ≤ 11 / 10 := by
  have hexp : 64 * γ ≤ 1 / 40 := by nlinarith [hγ]
  have hmono := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 20) hexp
  have hrootLe : Real.rpow 20 (1 / 40 : ℝ) ≤ 11 / 10 := by
    have hroot : (Real.rpow 20 (1 / 40 : ℝ)) ^ 40 = 20 := by
      have h := Real.rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 20)
        (by norm_num : 40 ≠ 0)
      convert h using 1 <;> norm_num
    have h11 : 20 ≤ (11 / 10 : ℝ) ^ 40 := by norm_num
    apply (pow_le_pow_iff_left₀
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 20) _)
      (by norm_num : (0 : ℝ) ≤ 11 / 10) (by norm_num : 40 ≠ 0)).mp
    change (Real.rpow 20 (1 / 40 : ℝ)) ^ 40 ≤ (11 / 10 : ℝ) ^ 40
    rw [hroot]
    exact h11
  exact hmono.trans hrootLe

private noncomputable def aoPerDepthTargetCoefficient
    (γ q : ℝ) (t : ℕ) : ℝ :=
  2700000 * γ * q + 11700000 * γ + 4350000 * γ * q * (t : ℝ)

private theorem aoPerDepth_four_to_five_factor {γ : ℝ} {t : ℕ}
    (hγ : 0 ≤ γ) :
    (3 : ℝ) ^ (4 * γ * ((t : ℝ) + 1)) ≤
      (3 : ℝ) ^ (5 * γ * ((t : ℝ) + 1)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
  nlinarith [hγ, show 0 ≤ (t : ℝ) + 1 by positivity]

private theorem aoPerDepth_raw_high_tzero_budget {γ q : ℝ}
    (hγ : 0 ≤ γ) (hseed : 1 / 19000 < γ * q)
    (hq20 : 20 ≤ q) (hpow : q ^ (64 * γ) ≤ 10 / 3) :
    aoPerDepthRawBound γ q 0 ≤
      aoPerDepthTargetCoefficient γ q 0 * (3 : ℝ) ^ (5 * γ) := by
  have hcoeff : (16 + 22480 * γ * q * (0 + 22 : ℝ)) * q ^ (64 * γ) ≤
      aoPerDepthTargetCoefficient γ q 0 := by
    have hcoeff' : (16 + 494560 * (γ * q)) * q ^ (64 * γ) ≤
        160 / 3 + (4945600 / 3) * (γ * q) := by
      have hpowMul' := mul_le_mul_of_nonneg_left hpow
        (by positivity : 0 ≤ 16 + 494560 * (γ * q))
      nlinarith [hpowMul']
    have hcoeffRaw : (16 + 494560 * (γ * q)) * q ^ (64 * γ) ≤
        2700000 * γ * q + 11700000 * γ := by
      nlinarith [hcoeff', hseed, hγ]
    have hcoeffRaw' :
        (16 + 22480 * γ * q * (0 + 22 : ℝ)) * q ^ (64 * γ) ≤
          2700000 * γ * q + 11700000 * γ := by
      simpa only [show 22480 * γ * q * (0 + 22 : ℝ) =
        494560 * (γ * q) by ring] using hcoeffRaw
    simpa [aoPerDepthTargetCoefficient] using hcoeffRaw'
  have hfactor := aoPerDepth_four_to_five_factor hγ (t := 0)
  have hcoefNonneg : 0 ≤ aoPerDepthTargetCoefficient γ q 0 := by
    dsimp [aoPerDepthTargetCoefficient]
    positivity
  have hfinal :
      (16 + 22480 * γ * q * (0 + 22 : ℝ)) * q ^ (64 * γ) *
          (3 : ℝ) ^ (4 * γ * ((0 : ℕ) + 1)) ≤
        aoPerDepthTargetCoefficient γ q 0 *
          (3 : ℝ) ^ (5 * γ * ((0 : ℕ) + 1)) := by
    calc
      _ ≤ aoPerDepthTargetCoefficient γ q 0 *
          (3 : ℝ) ^ (4 * γ * ((0 : ℕ) + 1)) :=
        mul_le_mul_of_nonneg_right hcoeff
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hfactor hcoefNonneg
  simpa [aoPerDepthRawBound, Nat.cast_zero, zero_add, zero_div] using hfinal

private theorem aoPerDepth_raw_high_positive_budget {γ q : ℝ} {t : ℕ}
    (hγ : 0 ≤ γ) (ht : 0 < t) (hseed :
      1 / 19000 < γ * q ∨ 1 / 1536 < γ * q * (t : ℝ))
    (hq20 : 20 ≤ q) (hqDepth : 4 + 3 * (t : ℝ) ≤ q)
    (hpow : q ^ (64 * γ) ≤ 10 / 3) :
    aoPerDepthRawBound γ q t ≤
      aoPerDepthTargetCoefficient γ q t *
        (3 : ℝ) ^ (5 * γ * ((t : ℝ) + 1)) := by
  have hqpos : 0 < q := by linarith
  have hpop := aoPerDepth_population_le (q := q) (t := t) hqDepth
  have hshape : 0 ≤ 16 + 22480 * γ * q * ((t : ℝ) + 22) := by positivity
  have hpopPow : Real.rpow 9 ((t : ℝ) / q) * q ^ (64 * γ) ≤ 7 := by
    calc
      Real.rpow 9 ((t : ℝ) / q) * q ^ (64 * γ) ≤
          (21 / 10) * q ^ (64 * γ) :=
        mul_le_mul_of_nonneg_right hpop (by positivity)
      _ ≤ (21 / 10) * (10 / 3) :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = 7 := by norm_num
  have hrawCoeff : Real.rpow 9 ((t : ℝ) / q) * q ^ (64 * γ) *
      (16 + 22480 * γ * q * ((t : ℝ) + 22)) ≤
      7 * (16 + 22480 * γ * q * ((t : ℝ) + 22)) :=
    mul_le_mul_of_nonneg_right hpopPow hshape
  have htpos : 0 < (t : ℝ) := by exact_mod_cast ht
  have ht1Nat : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt ht)
  have ht1 : 1 ≤ (t : ℝ) := by exact_mod_cast ht1Nat
  have hgammaq : 0 ≤ γ * q := mul_nonneg hγ (by linarith)
  have hgammaqt : 0 ≤ γ * q * (t : ℝ) := mul_nonneg hgammaq htpos.le
  have htarget : 7 * (16 + 22480 * γ * q * ((t : ℝ) + 22)) ≤
      aoPerDepthTargetCoefficient γ q t := by
    by_cases hfirst : 1 / 19000 < γ * q
    · have htime : (t : ℝ) + 22 ≤ 23 * (t : ℝ) := by nlinarith [ht1]
      have hvar : γ * q * ((t : ℝ) + 22) ≤ γ * q * (23 * (t : ℝ)) :=
        mul_le_mul_of_nonneg_left htime hgammaq
      dsimp [aoPerDepthTargetCoefficient]
      nlinarith [hfirst, hvar]
    · have hsecond : 1 / 1536 < γ * q * (t : ℝ) := hseed.resolve_left hfirst
      by_cases ht7 : (t : ℝ) ≤ 7
      · have hgammaqLower : 1 / 10752 < γ * q := by
          have hmul := mul_le_mul_of_nonneg_left ht7 hgammaq
          nlinarith [hsecond]
        have htime : (t : ℝ) + 22 ≤ 23 * (t : ℝ) := by nlinarith [ht1]
        have hvar : γ * q * ((t : ℝ) + 22) ≤ γ * q * (23 * (t : ℝ)) :=
          mul_le_mul_of_nonneg_left htime hgammaq
        dsimp [aoPerDepthTargetCoefficient]
        nlinarith [hgammaqLower, hvar]
      · have htgt7 : 7 < (t : ℝ) := lt_of_not_ge ht7
        have htgt7Nat : 7 < t := by exact_mod_cast htgt7
        have ht8Nat : 8 ≤ t := by omega
        have ht8 : 8 ≤ (t : ℝ) := by exact_mod_cast ht8Nat
        have htime : (t : ℝ) + 22 ≤ 4 * (t : ℝ) := by nlinarith [ht8]
        have hvar : γ * q * ((t : ℝ) + 22) ≤ γ * q * (4 * (t : ℝ)) :=
          mul_le_mul_of_nonneg_left htime hgammaq
        dsimp [aoPerDepthTargetCoefficient]
        nlinarith [hsecond, hvar]
  have hfactor := aoPerDepth_four_to_five_factor (t := t) hγ
  have hcoefNonneg : 0 ≤ aoPerDepthTargetCoefficient γ q t := by
    dsimp [aoPerDepthTargetCoefficient]
    positivity
  have hrawCoeff' := hrawCoeff.trans htarget
  calc
    aoPerDepthRawBound γ q t =
        (Real.rpow 9 ((t : ℝ) / q) * q ^ (64 * γ) *
          (16 + 22480 * γ * q * ((t : ℝ) + 22))) *
          (3 : ℝ) ^ (4 * γ * ((t : ℝ) + 1)) := by
      dsimp [aoPerDepthRawBound]
      ring
    _ ≤ aoPerDepthTargetCoefficient γ q t *
          (3 : ℝ) ^ (4 * γ * ((t : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hrawCoeff'
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hfactor hcoefNonneg

/-- The reset profile, followed by its raw polynomial envelope, bounds the
depth maximum at any order lowered from `R`. -/
private theorem aoPerDepth_raw_profile_bound
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    (m : ℤ) (q R : ℝ) (hqR : q ≤ R)
    (hR : 20 ≤ R) (t : ℕ) :
    eLpNorm (fun ω => ENNReal.ofReal (cutoffTraceDefectMaxAtDepth M m ω t))
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aoPerDepthRawBound M.gamma R t) := by
  have hR2 : 2 ≤ R := by linarith [hR]
  have hmax := aoPerDepth_max_reset_profile reset M h hM hγ hstate m R hR2 t
  have hmono : eLpNorm
      (fun ω => ENNReal.ofReal (cutoffTraceDefectMaxAtDepth M m ω t))
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      eLpNorm (fun ω => ENNReal.ofReal (cutoffTraceDefectMaxAtDepth M m ω t))
        (ENNReal.ofReal R) (Cutoff.cutoffSampleLaw M).toMeasure := by
    exact eLpNorm_le_eLpNorm_of_exponent_le
      (ENNReal.ofReal_le_ofReal hqR)
  have hprofile := aoPerDepth_raw_envelope (t := t)
    (le_of_lt M.shellPrefix.gamma_pos) (by simpa only [gammaZero] using hγ)
    hR
  have hpop : 0 ≤ Real.rpow 9 ((t : ℝ) / R) :=
    Real.rpow_nonneg (by norm_num) _
  have hscalar :
      Real.rpow 9 ((t : ℝ) / R) *
          Inverse.orderTraceProfile M.gamma R ((t : ℝ) + 1) ((t : ℝ) + 1) ≤
        aoPerDepthRawBound M.gamma R t := by
    calc
      _ ≤ Real.rpow 9 ((t : ℝ) / R) *
          ((16 + 22480 * M.gamma * R * ((t : ℝ) + 22)) *
            R ^ (64 * M.gamma) * (3 : ℝ) ^ (4 * M.gamma * ((t : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hprofile hpop
      _ = aoPerDepthRawBound M.gamma R t := by
        dsimp [aoPerDepthRawBound]
        ring
  calc
    _ ≤ eLpNorm (fun ω => ENNReal.ofReal (cutoffTraceDefectMaxAtDepth M m ω t))
        (ENNReal.ofReal R) (Cutoff.cutoffSampleLaw M).toMeasure := hmono
    _ ≤ ENNReal.ofReal (Real.rpow 9 ((t : ℝ) / R)) *
        ENNReal.ofReal (Inverse.orderTraceProfile M.gamma R
          ((t : ℝ) + 1) ((t : ℝ) + 1)) := hmax
    _ ≤ ENNReal.ofReal (aoPerDepthRawBound M.gamma R t) := by
      rw [← ENNReal.ofReal_mul hpop]
      exact ENNReal.ofReal_le_ofReal hscalar

private theorem aoPerDepth_raw_low_budget {γ q : ℝ} {t : ℕ}
    (hγ : 0 ≤ γ) (hγlower : 1 / 327680 < γ)
    (hγmax : γ ≤ 17 / 50000) (hqDepth : 4 + 3 * (t : ℝ) ≤ q)
    (hq20 : q < 20) (ht : 0 < t) :
    aoPerDepthRawBound γ 20 t ≤
      aoPerDepthTargetCoefficient γ q t *
        (3 : ℝ) ^ (5 * γ * ((t : ℝ) + 1)) := by
  have hqpos : 0 < q := by linarith [hqDepth]
  have ht1 : 1 ≤ (t : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt ht))
  have ht5 : t ≤ 5 := by
    have htCast : 3 * (t : ℝ) < 16 := by linarith [hqDepth, hq20]
    have htNat : 3 * t < 16 := by exact_mod_cast htCast
    omega
  have hpop := aoPerDepth_population_two_le (t := t) ht5
  have hpow20 := aoPerDepth_twenty_power_le (γ := γ) hγmax
  have htime : 20 * ((t : ℝ) + 22) ≤ 66 * q * (t : ℝ) := by
    have hqt : 0 ≤ q * (t : ℝ) := mul_nonneg hqpos.le (by positivity)
    nlinarith [hqDepth, hq20, ht1, hqt]
  have hshape : 0 ≤ 16 + 22480 * γ * 20 * ((t : ℝ) + 22) := by positivity
  have hpopPow : Real.rpow 9 ((t : ℝ) / 20) * 20 ^ (64 * γ) ≤ 11 / 5 := by
    calc
      _ ≤ 2 * (11 / 10 : ℝ) := mul_le_mul hpop hpow20 (by positivity) (by positivity)
      _ = 11 / 5 := by norm_num
  have hcoeff : Real.rpow 9 ((t : ℝ) / 20) *
      (16 + 22480 * γ * 20 * ((t : ℝ) + 22)) * 20 ^ (64 * γ) ≤
        aoPerDepthTargetCoefficient γ q t := by
    have hcoeff' : (11 / 5 : ℝ) *
        (16 + 22480 * γ * 20 * ((t : ℝ) + 22)) ≤
          aoPerDepthTargetCoefficient γ q t := by
      dsimp [aoPerDepthTargetCoefficient]
      nlinarith [htime, hqDepth, hqpos, ht1, hγlower]
    calc
      _ = (Real.rpow 9 ((t : ℝ) / 20) * 20 ^ (64 * γ)) *
          (16 + 22480 * γ * 20 * ((t : ℝ) + 22)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hpopPow hshape
      _ ≤ _ := hcoeff'
  have hfactor := aoPerDepth_four_to_five_factor (t := t) hγ
  have htargetNonneg : 0 ≤ aoPerDepthTargetCoefficient γ q t := by
    dsimp [aoPerDepthTargetCoefficient]
    positivity
  calc
    aoPerDepthRawBound γ 20 t =
        (Real.rpow 9 ((t : ℝ) / 20) *
          (16 + 22480 * γ * 20 * ((t : ℝ) + 22)) * 20 ^ (64 * γ)) *
          (3 : ℝ) ^ (4 * γ * ((t : ℝ) + 1)) := by
      dsimp [aoPerDepthRawBound]
    _ ≤ aoPerDepthTargetCoefficient γ q t *
        (3 : ℝ) ^ (4 * γ * ((t : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hcoeff
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hfactor htargetNonneg

private theorem aoPerDepth_raw_high_rare_budget {γ q : ℝ} {t : ℕ}
    (hγ0 : 0 ≤ γ) (hγpos : 0 < γ) (hγmax : γ ≤ 17 / 50000)
    (hq20 : 20 ≤ q) (hqDepth : 4 + 3 * (t : ℝ) ≤ q)
    (hpow : 10 / 3 < q ^ (64 * γ)) :
    aoPerDepthRawBound γ q t ≤
      Real.exp (-(Real.log 2 / (64 * γ))) * q ^ 3 *
        (3 : ℝ) ^ (5 * γ * ((t : ℝ) + 1)) := by
  have hqpos : 0 < q := by linarith
  have hαpos : 0 < 64 * γ := by positivity
  have hαle : 64 * γ ≤ 1 / 45 := by nlinarith [hγmax]
  have hInvα : 45 ≤ 1 / (64 * γ) := by
    apply (le_div_iff₀ hαpos).2
    nlinarith [hαle]
  have hlog2upper : Real.log 2 < 7 / 10 :=
    lt_of_le_of_lt Numerics.log_two_enclosure.2 (by norm_num)
  have hlog103 : Real.log (10 / 3 : ℝ) < 7 / 5 := by
    have hlt : (10 / 3 : ℝ) < 4 := by norm_num
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 10 / 3) hlt
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
    nlinarith [h, hlog2upper]
  have hlog109 : (1 / 10 : ℝ) ≤ Real.log (10 / 9) := by
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9 / 10)
    have hinv : (10 / 9 : ℝ) = (9 / 10)⁻¹ := by norm_num
    rw [hinv, Real.log_inv]
    norm_num at hlog ⊢
    linarith
  have hlog53 : (1 / 2 : ℝ) < Real.log (5 / 3) := by
    have hmul : (5 / 3 : ℝ) = (3 / 2) * (10 / 9) := by norm_num
    rw [hmul, Real.log_mul (by norm_num) (by norm_num)]
    have hlog32 := Numerics.log_three_halves_enclosure.1
    linarith [hlog32, hlog109]
  have hlogpow : Real.log (10 / 3 : ℝ) < (64 * γ) * Real.log q := by
    rw [← Real.log_rpow hqpos]
    exact Real.log_lt_log (by norm_num : (0 : ℝ) < 10 / 3) hpow
  have hlogq : Real.log (10 / 3 : ℝ) / (64 * γ) < Real.log q :=
    (div_lt_iff₀ hαpos).2 (by simpa only [mul_comm] using hlogpow)
  have hepsq : (2 : ℝ) ^ 30 <
      Real.exp (-(Real.log 2 / (64 * γ))) * q ^ (1 - 64 * γ) := by
    have hlogeps : Real.log (Real.exp (-(Real.log 2 / (64 * γ)))) =
        -(Real.log 2 / (64 * γ)) := Real.log_exp _
    have hlogqpow : Real.log (q ^ (1 - 64 * γ)) =
        (1 - 64 * γ) * Real.log q := Real.log_rpow hqpos _
    have hlogProd : Real.log (Real.exp (-(Real.log 2 / (64 * γ))) *
        q ^ (1 - 64 * γ)) =
        -(Real.log 2 / (64 * γ)) + (1 - 64 * γ) * Real.log q := by
      rw [Real.log_mul (ne_of_gt (Real.exp_pos _))
        (ne_of_gt (Real.rpow_pos_of_pos hqpos _)), hlogeps, hlogqpow]
    have hlogmul :
        30 * Real.log 2 <
          -(Real.log 2 / (64 * γ)) + (1 - 64 * γ) * Real.log q := by
      have hlog53over : 45 * (1 / 2 : ℝ) <
          Real.log (5 / 3) / (64 * γ) := by
        have hlog53pos : 0 ≤ Real.log (5 / 3) := by linarith [hlog53]
        calc
          45 * (1 / 2 : ℝ) < 45 * Real.log (5 / 3) := by nlinarith [hlog53]
          _ = Real.log (5 / 3) * 45 := by ring
          _ ≤ Real.log (5 / 3) * (1 / (64 * γ)) :=
            mul_le_mul_of_nonneg_left hInvα hlog53pos
          _ = Real.log (5 / 3) / (64 * γ) := by ring
      have hlogidentity :
          (Real.log (10 / 3) / (64 * γ) - Real.log 2 / (64 * γ)) -
              Real.log (10 / 3) =
            Real.log (5 / 3) / (64 * γ) - Real.log (10 / 3) := by
        have hlogmul23 : Real.log (10 / 3) - Real.log 2 = Real.log (5 / 3) := by
          have hmul : (10 / 3 : ℝ) = 2 * (5 / 3) := by norm_num
          rw [hmul, Real.log_mul (by norm_num) (by norm_num)]
          ring
        rw [← hlogmul23]
        ring
      have hlogsmall :
          Real.log (5 / 3) / (64 * γ) - Real.log (10 / 3) > 211 / 10 := by
        linarith [hlog53over, hlog103]
      have hlog2cap : 30 * Real.log 2 < 21 := by nlinarith [hlog2upper]
      have hnonneg : 0 ≤ 1 - 64 * γ := by linarith [hαle]
      have hOneMinus : 0 < 1 - 64 * γ := by linarith [hαle]
      have hstrict := mul_lt_mul_of_pos_left hlogq hOneMinus
      have hbase : -(Real.log 2 / (64 * γ)) +
          (1 - 64 * γ) * (Real.log (10 / 3) / (64 * γ)) =
          (Real.log (10 / 3) / (64 * γ) - Real.log 2 / (64 * γ)) -
            Real.log (10 / 3) := by
        field_simp [ne_of_gt hαpos]
        ring
      have hbaseLower : 21 < -(Real.log 2 / (64 * γ)) +
          (1 - 64 * γ) * (Real.log (10 / 3) / (64 * γ)) := by
        rw [hbase, hlogidentity]
        linarith [hlogsmall]
      linarith [hbaseLower, hstrict, hlog2cap]
    have hexp := Real.exp_lt_exp.mpr hlogmul
    have hpow2 : Real.exp (30 * Real.log 2) = (2 : ℝ) ^ 30 := by
      have hlogpow2 : Real.log ((2 : ℝ) ^ 30) = 30 * Real.log 2 := by
        rw [Real.log_pow]
        norm_num
      rw [← hlogpow2, Real.exp_log (by positivity)]
    rw [hpow2] at hexp
    have hlogpositive : 0 <
        Real.exp (-(Real.log 2 / (64 * γ))) * q ^ (1 - 64 * γ) :=
      mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hqpos _)
    have hconvert : Real.exp (-(Real.log 2 / (64 * γ)) +
        (1 - 64 * γ) * Real.log q) =
        Real.exp (-(Real.log 2 / (64 * γ))) * q ^ (1 - 64 * γ) := by
      rw [← hlogProd, Real.exp_log hlogpositive]
    exact hexp.trans_eq hconvert
  have htime : (t : ℝ) + 22 ≤ 2 * q := by
    have htBound : 3 * (t : ℝ) ≤ q - 4 := by linarith [hqDepth]
    nlinarith [hq20, htBound]
  have hgammaLeOne : γ ≤ 1 := by linarith [hγmax]
  have hshape : 0 ≤ 16 + 22480 * γ * q * ((t : ℝ) + 22) := by positivity
  have hpop := aoPerDepth_population_le (q := q) (t := t) hqDepth
  have hpopulationShape :
      Real.rpow 9 ((t : ℝ) / q) *
        (16 + 22480 * γ * q * ((t : ℝ) + 22)) ≤ 100000 * q ^ 2 := by
    have htimeShape :
        16 + 22480 * γ * q * ((t : ℝ) + 22) ≤ 16 + 44960 * γ * q ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left htime
        (mul_nonneg (show (0 : ℝ) ≤ 22480 by norm_num)
          (mul_nonneg hγ0 hqpos.le))
      nlinarith [hmul]
    have hshapeBound :
        16 + 44960 * γ * q ^ 2 ≤ 45000 * q ^ 2 := by
      have hqSq : 0 ≤ q ^ 2 := sq_nonneg q
      have hgammaSq := mul_le_mul_of_nonneg_right hgammaLeOne hqSq
      nlinarith [hgammaSq, hqSq, hq20]
    calc
      _ ≤ (21 / 10 : ℝ) *
          (16 + 22480 * γ * q * ((t : ℝ) + 22)) :=
        mul_le_mul_of_nonneg_right hpop hshape
      _ ≤ (21 / 10 : ℝ) * (45000 * q ^ 2) :=
        mul_le_mul_of_nonneg_left (htimeShape.trans hshapeBound) (by norm_num)
      _ ≤ 100000 * q ^ 2 := by nlinarith [sq_nonneg q]
  have hrareCoefficient :
      Real.rpow 9 ((t : ℝ) / q) *
        (16 + 22480 * γ * q * ((t : ℝ) + 22)) * q ^ (64 * γ) ≤
          Real.exp (-(Real.log 2 / (64 * γ))) * q ^ 3 := by
    have hqpowpos : 0 < q ^ (64 * γ) := Real.rpow_pos_of_pos hqpos _
    have hscale := mul_le_mul_of_nonneg_right hpopulationShape hqpowpos.le
    have htarget := mul_lt_mul_of_pos_right hepsq (sq_pos_of_pos hqpos)
    have hfactor : q ^ (1 - 64 * γ) * q ^ (64 * γ) = q := by
      rw [← Real.rpow_add hqpos]
      rw [show (1 - 64 * γ) + (64 * γ) = 1 by ring, Real.rpow_one]
    have htarget' : (2 : ℝ) ^ 30 * q ^ 2 * q ^ (64 * γ) <
        Real.exp (-(Real.log 2 / (64 * γ))) * q ^ 3 := by
      calc
        _ < Real.exp (-(Real.log 2 / (64 * γ))) *
              q ^ (1 - 64 * γ) * q ^ 2 * q ^ (64 * γ) :=
          mul_lt_mul_of_pos_right htarget hqpowpos
        _ = _ := by
          calc
            Real.exp (-(Real.log 2 / (64 * γ))) * q ^ (1 - 64 * γ) *
                q ^ 2 * q ^ (64 * γ) =
              Real.exp (-(Real.log 2 / (64 * γ))) *
                (q ^ (1 - 64 * γ) * q ^ (64 * γ)) * q ^ 2 := by ring
            _ = Real.exp (-(Real.log 2 / (64 * γ))) * q ^ 3 := by
              rw [hfactor]
              ring
    have hconst : 100000 ≤ (2 : ℝ) ^ 30 := by norm_num
    have hcoeff : 100000 * q ^ 2 * q ^ (64 * γ) ≤
        (2 : ℝ) ^ 30 * q ^ 2 * q ^ (64 * γ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst
        (sq_nonneg q)) hqpowpos.le
    exact le_trans hscale (le_trans hcoeff htarget'.le)
  have hfactor := aoPerDepth_four_to_five_factor (t := t) hγ0
  have hframeNonneg : 0 ≤ (3 : ℝ) ^ (4 * γ * ((t : ℝ) + 1)) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    aoPerDepthRawBound γ q t =
        (Real.rpow 9 ((t : ℝ) / q) *
          (16 + 22480 * γ * q * ((t : ℝ) + 22)) * q ^ (64 * γ)) *
          (3 : ℝ) ^ (4 * γ * ((t : ℝ) + 1)) := by
      dsimp [aoPerDepthRawBound]
    _ ≤ (Real.exp (-(Real.log 2 / (64 * γ))) * q ^ 3) *
        (3 : ℝ) ^ (4 * γ * ((t : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hrareCoefficient hframeNonneg
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left hfactor
      positivity

private theorem aoPerDepth_native_zero_budget {γ q : ℝ}
    (hγ : 0 ≤ γ) (hq4 : 4 ≤ q) (hgammaq : 0 ≤ γ * q) :
    900000 * γ * (if q < 12 then 12 else q + 2) ≤
      aoPerDepthTargetCoefficient γ q 0 := by
  by_cases hq12 : q < 12
  · rw [if_pos hq12]
    dsimp [aoPerDepthTargetCoefficient]
    nlinarith [hγ, hq4]
  · have hq12' : ¬ q < 12 := hq12
    rw [if_neg hq12']
    dsimp [aoPerDepthTargetCoefficient]
    nlinarith [hgammaq]

private theorem aoPerDepth_direct_budget {γ q : ℝ} {t : ℕ}
    (hγ : 0 ≤ γ) (ht : 0 < t) (hqDepth : 4 + 3 * (t : ℝ) ≤ q)
    (hframe : (3 : ℝ) ^ (2 * γ * (t : ℝ)) ≤ 10008 / 10000) :
    (Real.rpow 9 ((t : ℝ) / q)) *
      ((1017 / 1000 : ℝ) *
        (900000 * γ * (q + 2) +
          (t : ℝ) * (19 * q * (9 / 2 : ℝ) * γ *
            (3 : ℝ) ^ (2 * γ * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120))) +
        4 * γ * q * (t : ℝ) * (3 : ℝ) ^ (2 * γ * (t : ℝ))) ≤
      aoPerDepthTargetCoefficient γ q t := by
  have hqpos : 0 < q := by linarith [hqDepth]
  have hpop := aoPerDepth_population_le (q := q) (t := t) hqDepth
  have hpop3 : Real.rpow 9 ((t : ℝ) / q) ≤ 3 := hpop.trans (by norm_num)
  have hFnonneg : 0 ≤ (3 : ℝ) ^ (2 * γ * (t : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hγqNonneg : 0 ≤ γ * q := mul_nonneg hγ hqpos.le
  have hγqtNonneg : 0 ≤ γ * q * (t : ℝ) :=
    mul_nonneg hγqNonneg (by positivity)
  have hbaseNonneg : 0 ≤ 900000 * γ * (q + 2) := by positivity
  have hbase : Real.rpow 9 ((t : ℝ) / q) *
      ((1017 / 1000 : ℝ) * (900000 * γ * (q + 2))) ≤
        3 * (1017 / 1000 : ℝ) * (900000 * γ * (q + 2)) := by
    have hbaseCoeff : 0 ≤ (1017 / 1000 : ℝ) *
        (900000 * γ * (q + 2)) := by positivity
    calc
      _ ≤ 3 * ((1017 / 1000 : ℝ) * (900000 * γ * (q + 2))) :=
        mul_le_mul_of_nonneg_right hpop3 hbaseCoeff
      _ = 3 * (1017 / 1000 : ℝ) * (900000 * γ * (q + 2)) := by ring
  have htransFactor :
      Real.rpow 9 ((t : ℝ) / q) *
        ((1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
          ((2.2 : ℝ) ^ 2 * 3120) * (3 : ℝ) ^ (2 * γ * (t : ℝ)) +
          4 * (3 : ℝ) ^ (2 * γ * (t : ℝ))) ≤ 4000000 := by
    have hC : 0 ≤
        (1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
          ((2.2 : ℝ) ^ 2 * 3120) := by positivity
    have hframeC := mul_le_mul_of_nonneg_left hframe hC
    have hframe4 := mul_le_mul_of_nonneg_left hframe (by norm_num : (0 : ℝ) ≤ 4)
    have hcoeff :
        (1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
            ((2.2 : ℝ) ^ 2 * 3120) * (3 : ℝ) ^ (2 * γ * (t : ℝ)) +
          4 * (3 : ℝ) ^ (2 * γ * (t : ℝ)) ≤
        (10008 / 10000 : ℝ) *
          ((1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
            ((2.2 : ℝ) ^ 2 * 3120) + 4) := by
      nlinarith [hframeC, hframe4]
    have hcoeffNonneg : 0 ≤
        (1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
            ((2.2 : ℝ) ^ 2 * 3120) * (3 : ℝ) ^ (2 * γ * (t : ℝ)) +
          4 * (3 : ℝ) ^ (2 * γ * (t : ℝ)) := by positivity
    calc
      _ ≤ 3 * ((1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
          ((2.2 : ℝ) ^ 2 * 3120) * (3 : ℝ) ^ (2 * γ * (t : ℝ)) +
          4 * (3 : ℝ) ^ (2 * γ * (t : ℝ))) :=
        mul_le_mul_of_nonneg_right hpop3 hcoeffNonneg
      _ ≤ 3 * ((10008 / 10000 : ℝ) *
          ((1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
            ((2.2 : ℝ) ^ 2 * 3120) + 4)) :=
        mul_le_mul_of_nonneg_left hcoeff (by norm_num)
      _ ≤ 4000000 := by norm_num
  have htrans : Real.rpow 9 ((t : ℝ) / q) *
      ((1017 / 1000 : ℝ) *
        ((t : ℝ) * (19 * q * (9 / 2 : ℝ) * γ *
          (3 : ℝ) ^ (2 * γ * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120))) +
        4 * γ * q * (t : ℝ) * (3 : ℝ) ^ (2 * γ * (t : ℝ))) ≤
        4000000 * γ * q * (t : ℝ) := by
    have hfac :
        (1017 / 1000 : ℝ) *
            (19 * q * (9 / 2 : ℝ) * γ *
              (3 : ℝ) ^ (2 * γ * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120)) +
          4 * γ * q * (3 : ℝ) ^ (2 * γ * (t : ℝ)) =
          γ * q * ((1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
            ((2.2 : ℝ) ^ 2 * 3120) * (3 : ℝ) ^ (2 * γ * (t : ℝ)) +
            4 * (3 : ℝ) ^ (2 * γ * (t : ℝ))) := by ring
    calc
      _ = (γ * q * (t : ℝ)) *
          (Real.rpow 9 ((t : ℝ) / q) *
            ((1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
              ((2.2 : ℝ) ^ 2 * 3120) * (3 : ℝ) ^ (2 * γ * (t : ℝ)) +
             4 * (3 : ℝ) ^ (2 * γ * (t : ℝ)))) := by
        ring
      _ ≤ (γ * q * (t : ℝ)) * 4000000 :=
        mul_le_mul_of_nonneg_left htransFactor hγqtNonneg
      _ = 4000000 * γ * q * (t : ℝ) := by ring
  have htarget :
      3 * (1017 / 1000 : ℝ) * (900000 * γ * (q + 2)) +
          4000000 * γ * q * (t : ℝ) ≤
        aoPerDepthTargetCoefficient γ q t := by
    have ht1 : 1 ≤ (t : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt ht))
    have hγqtLower : γ * q ≤ γ * q * (t : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left ht1 hγqNonneg]
    dsimp [aoPerDepthTargetCoefficient]
    nlinarith [hγ, hγqNonneg, ht1, hγqtLower]
  have hsum := add_le_add hbase htrans
  calc
    _ ≤ _ := by
      have hsplit : Real.rpow 9 ((t : ℝ) / q) *
          ((1017 / 1000 : ℝ) *
            (900000 * γ * (q + 2) +
              (t : ℝ) * (19 * q * (9 / 2 : ℝ) * γ *
                (3 : ℝ) ^ (2 * γ * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120))) +
            4 * γ * q * (t : ℝ) * (3 : ℝ) ^ (2 * γ * (t : ℝ))) =
          Real.rpow 9 ((t : ℝ) / q) *
            ((1017 / 1000 : ℝ) * (900000 * γ * (q + 2)) +
              (1017 / 1000 : ℝ) *
                ((t : ℝ) * (19 * q * (9 / 2 : ℝ) * γ *
                  (3 : ℝ) ^ (2 * γ * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120))) +
              4 * γ * q * (t : ℝ) * (3 : ℝ) ^ (2 * γ * (t : ℝ))) := by ring
      rw [hsplit]
      nlinarith [hbase, htrans]
    _ ≤ _ := htarget

private theorem aoPerDepth_direct_twelve_budget {γ q : ℝ} {t : ℕ}
    (hγ : 0 ≤ γ) (ht : 0 < t) (ht2 : t ≤ 2)
    (hqDepth : 4 + 3 * (t : ℝ) ≤ q)
    (hframe : (3 : ℝ) ^ (2 * γ * (t : ℝ)) ≤ 10008 / 10000) :
    (Real.rpow 9 ((t : ℝ) / 12)) *
      ((1017 / 1000 : ℝ) *
        (900000 * γ * (12 + 2) +
          (t : ℝ) * (19 * 12 * (9 / 2 : ℝ) * γ *
            (3 : ℝ) ^ (2 * γ * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120))) +
        4 * γ * 12 * (t : ℝ) * (3 : ℝ) ^ (2 * γ * (t : ℝ))) ≤
      aoPerDepthTargetCoefficient γ q t := by
  have ht1 : 1 ≤ (t : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt ht))
  have hq12depth : 4 + 3 * (t : ℝ) ≤ 12 := by
    have htcast : (t : ℝ) ≤ 2 := by exact_mod_cast ht2
    nlinarith
  have hpop := aoPerDepth_population_le (q := 12) (t := t) hq12depth
  have hbaseCoef : (21 / 10 : ℝ) * (1017 / 1000) *
      (900000 * 14) ≤ 27000000 := by norm_num
  have hframeNonneg : 0 ≤ (3 : ℝ) ^ (2 * γ * (t : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have htransCoef : (21 / 10 : ℝ) * (10008 / 10000) * 12 *
      ((1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
          ((2.2 : ℝ) ^ 2 * 3120) + 4) ≤ 33200000 := by norm_num
  have hbase : Real.rpow 9 ((t : ℝ) / 12) *
      ((1017 / 1000 : ℝ) * (900000 * γ * (12 + 2))) ≤
        27000000 * γ := by
    have hnonneg : 0 ≤ (1017 / 1000 : ℝ) * (900000 * γ * 14) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hpop hnonneg
    have hbaseCoefγ := mul_le_mul_of_nonneg_right hbaseCoef hγ
    nlinarith [hmul, hbaseCoefγ]
  have htrans : Real.rpow 9 ((t : ℝ) / 12) *
      ((1017 / 1000 : ℝ) *
        ((t : ℝ) * (19 * 12 * (9 / 2 : ℝ) * γ *
          (3 : ℝ) ^ (2 * γ * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120))) +
        4 * γ * 12 * (t : ℝ) * (3 : ℝ) ^ (2 * γ * (t : ℝ))) ≤
        33200000 * γ * (t : ℝ) := by
    have hfac :
        (1017 / 1000 : ℝ) *
            (19 * 12 * (9 / 2 : ℝ) * γ *
              (3 : ℝ) ^ (2 * γ * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120)) +
          4 * γ * 12 * (3 : ℝ) ^ (2 * γ * (t : ℝ)) =
          γ * 12 * ((1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
            ((2.2 : ℝ) ^ 2 * 3120) * (3 : ℝ) ^ (2 * γ * (t : ℝ)) +
            4 * (3 : ℝ) ^ (2 * γ * (t : ℝ))) := by ring
    have hcoefBound :
        (1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
            ((2.2 : ℝ) ^ 2 * 3120) * (3 : ℝ) ^ (2 * γ * (t : ℝ)) +
          4 * (3 : ℝ) ^ (2 * γ * (t : ℝ)) ≤
        (10008 / 10000 : ℝ) *
          ((1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
            ((2.2 : ℝ) ^ 2 * 3120) + 4) := by
      have hmul := mul_le_mul_of_nonneg_left hframe
        (by norm_num : (0 : ℝ) ≤
          (1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) * ((2.2 : ℝ) ^ 2 * 3120) + 4)
      nlinarith [hmul]
    have hpopNonneg : 0 ≤ Real.rpow 9 ((t : ℝ) / 12) :=
      Real.rpow_nonneg (by norm_num) _
    have htNonneg : 0 ≤ (t : ℝ) := by positivity
    have hgamma12t : 0 ≤ γ * 12 * (t : ℝ) :=
      mul_nonneg (mul_nonneg hγ (by norm_num)) htNonneg
    have hprodBound : Real.rpow 9 ((t : ℝ) / 12) *
        ((1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
            ((2.2 : ℝ) ^ 2 * 3120) * (3 : ℝ) ^ (2 * γ * (t : ℝ)) +
          4 * (3 : ℝ) ^ (2 * γ * (t : ℝ))) ≤
        (21 / 10 : ℝ) * (10008 / 10000) *
          ((1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
            ((2.2 : ℝ) ^ 2 * 3120) + 4) := by
      calc
        _ ≤ Real.rpow 9 ((t : ℝ) / 12) *
            ((10008 / 10000 : ℝ) *
              ((1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
                ((2.2 : ℝ) ^ 2 * 3120) + 4)) :=
          mul_le_mul_of_nonneg_left hcoefBound hpopNonneg
        _ ≤ (21 / 10 : ℝ) * (10008 / 10000) *
            ((1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
              ((2.2 : ℝ) ^ 2 * 3120) + 4) := by
          have hcap : 0 ≤ (10008 / 10000 : ℝ) *
              ((1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
                ((2.2 : ℝ) ^ 2 * 3120) + 4) := by positivity
          calc
            _ ≤ (21 / 10 : ℝ) * ((10008 / 10000 : ℝ) *
                ((1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
                  ((2.2 : ℝ) ^ 2 * 3120) + 4)) :=
              mul_le_mul_of_nonneg_right hpop hcap
            _ = _ := by ring
    calc
      _ = (γ * 12 * (t : ℝ)) *
          (Real.rpow 9 ((t : ℝ) / 12) *
            ((1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
              ((2.2 : ℝ) ^ 2 * 3120) * (3 : ℝ) ^ (2 * γ * (t : ℝ)) +
             4 * (3 : ℝ) ^ (2 * γ * (t : ℝ)))) := by
          ring
      _ ≤ (γ * 12 * (t : ℝ)) *
          ((21 / 10 : ℝ) * (10008 / 10000) *
            ((1017 / 1000 : ℝ) * 19 * (9 / 2 : ℝ) *
              ((2.2 : ℝ) ^ 2 * 3120) + 4)) :=
          mul_le_mul_of_nonneg_left hprodBound hgamma12t
      _ ≤ 33200000 * γ * (t : ℝ) := by
          have hcoefScaled := mul_le_mul_of_nonneg_right htransCoef
            (mul_nonneg hγ htNonneg)
          nlinarith [hcoefScaled]
  have htarget : 27000000 * γ + 33200000 * γ * (t : ℝ) ≤
      aoPerDepthTargetCoefficient γ q t := by
    have htCases : t = 1 ∨ t = 2 := by omega
    rcases htCases with htOne | htTwo
    · rw [htOne] at hqDepth ⊢
      have hq7 : 7 ≤ q := by norm_num at hqDepth ⊢; linarith
      have hγq : 7 * γ ≤ γ * q := by
        calc
          7 * γ = γ * 7 := by ring
          _ ≤ γ * q := mul_le_mul_of_nonneg_left hq7 hγ
      dsimp [aoPerDepthTargetCoefficient]
      nlinarith [hγq, hγ]
    · rw [htTwo] at hqDepth ⊢
      have hq10 : 10 ≤ q := by norm_num at hqDepth ⊢; linarith
      have hγq : 10 * γ ≤ γ * q := by
        calc
          10 * γ = γ * 10 := by ring
          _ ≤ γ * q := mul_le_mul_of_nonneg_left hq10 hγ
      dsimp [aoPerDepthTargetCoefficient]
      nlinarith [hγq, hγ]
  have hsum := add_le_add hbase htrans
  have hsplit :
      Real.rpow 9 ((t : ℝ) / 12) *
        ((1017 / 1000 : ℝ) *
          (900000 * γ * (12 + 2) +
            (t : ℝ) * (19 * 12 * (9 / 2 : ℝ) * γ *
              (3 : ℝ) ^ (2 * γ * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120))) +
          4 * γ * 12 * (t : ℝ) * (3 : ℝ) ^ (2 * γ * (t : ℝ))) =
      Real.rpow 9 ((t : ℝ) / 12) *
        ((1017 / 1000 : ℝ) * (900000 * γ * 14) +
          (1017 / 1000 : ℝ) *
            ((t : ℝ) * (19 * 12 * (9 / 2 : ℝ) * γ *
              (3 : ℝ) ^ (2 * γ * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120))) +
          4 * γ * 12 * (t : ℝ) * (3 : ℝ) ^ (2 * γ * (t : ℝ))) := by ring
  calc
    _ = Real.rpow 9 ((t : ℝ) / 12) *
          ((1017 / 1000 : ℝ) * (900000 * γ * (12 + 2))) +
        Real.rpow 9 ((t : ℝ) / 12) *
          ((1017 / 1000 : ℝ) * ((t : ℝ) *
            (19 * 12 * (9 / 2 : ℝ) * γ *
              (3 : ℝ) ^ (2 * γ * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120))) +
           4 * γ * 12 * (t : ℝ) * (3 : ℝ) ^ (2 * γ * (t : ℝ))) := by
          rw [hsplit]
          ring
    _ ≤ aoPerDepthTargetCoefficient γ q t := hsum.trans htarget

private theorem aoPerDepth_trace_nonneg_at (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    0 ≤ traceDefect (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ) := by
  obtain ⟨Λ, hEll⟩ := Variational.cutoff_isEllipticFieldOn_cube M m ω Q
  exact Variational.traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos
    hEll (Annealed.sigmaBar_characterization M m).1

private theorem aoPerDepth_depth_max_nonneg (M : ABKModel 2) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) (t : ℕ) :
    0 ≤ cutoffTraceDefectMaxAtDepth M m ω t := by
  unfold cutoffTraceDefectMaxAtDepth
  apply Book.Ch02.finsetSupReal_nonneg
  intro Q _hQ
  exact aoPerDepth_trace_nonneg_at M m Q ω

private theorem aoPerDepth_bulk_profile_bound {γ p : ℝ} {t : ℕ}
    (hγ : 0 ≤ γ) (hγpos : 0 < γ) (hp : 1 ≤ p) :
    aoPerDepthTargetCoefficient γ (p + 3 * (t : ℝ) + 3) t *
        (3 : ℝ) ^ (5 * γ * ((t : ℝ) + 1)) ≤
      allOrderDepthProfile γ p t := by
  have hrare : 0 ≤ Real.exp (-(Real.log 2 / (64 * γ))) *
      (p + 3 * (t : ℝ) + 3) ^ 3 *
        (3 : ℝ) ^ (5 * γ * ((t : ℝ) + 1)) := by
    positivity
  have hcoeff : aoPerDepthTargetCoefficient γ
      (p + 3 * (t : ℝ) + 3) t =
      3 * 900000 * γ * (p + 3 * (t : ℝ) + 3) +
        13 * 900000 * γ + 4350000 * γ *
          (p + 3 * (t : ℝ) + 3) * (t : ℝ) := by
    dsimp [aoPerDepthTargetCoefficient]
    ring
  unfold allOrderDepthProfile
  dsimp
  rw [hcoeff]
  exact le_add_of_nonneg_right hrare

private theorem aoPerDepth_rare_profile_bound {γ p : ℝ} {t : ℕ}
    (hγpos : 0 < γ) (hp : 1 ≤ p) :
    Real.exp (-(Real.log 2 / (64 * γ))) *
        (p + 3 * (t : ℝ) + 3) ^ 3 *
        (3 : ℝ) ^ (5 * γ * ((t : ℝ) + 1)) ≤
      allOrderDepthProfile γ p t := by
  have hq : 0 ≤ p + 3 * (t : ℝ) + 3 := by positivity
  have hbulk : 0 ≤ aoPerDepthTargetCoefficient γ
      (p + 3 * (t : ℝ) + 3) t *
        (3 : ℝ) ^ (5 * γ * ((t : ℝ) + 1)) := by
    have hγ : 0 ≤ γ := hγpos.le
    have hcoeff : 0 ≤ aoPerDepthTargetCoefficient γ
        (p + 3 * (t : ℝ) + 3) t := by
      dsimp [aoPerDepthTargetCoefficient]
      positivity
    exact mul_nonneg hcoeff (Real.rpow_nonneg (by norm_num) _)
  have hcoeff : aoPerDepthTargetCoefficient γ
      (p + 3 * (t : ℝ) + 3) t =
      3 * 900000 * γ * (p + 3 * (t : ℝ) + 3) +
        13 * 900000 * γ + 4350000 * γ *
          (p + 3 * (t : ℝ) + 3) * (t : ℝ) := by
    dsimp [aoPerDepthTargetCoefficient]
    ring
  unfold allOrderDepthProfile
  dsimp
  have hbulk' : 0 ≤
      (3 * 900000 * γ * (p + 3 * (t : ℝ) + 3) +
        13 * 900000 * γ + 4350000 * γ *
          (p + 3 * (t : ℝ) + 3) * (t : ℝ)) *
        (3 : ℝ) ^ (5 * γ * ((t : ℝ) + 1)) := by
    rw [← hcoeff]
    exact hbulk
  exact le_add_of_nonneg_left hbulk'

/-- Conditional source theorem AO-PER-DEPTH. The only extra hypothesis is the
order-reset producer; the public source wrapper below instantiates it. -/
theorem ao_per_depth_of_reset (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    (m : ℤ) {p : ℝ} (hp : 1 ≤ p) (t : ℕ) :
    eLpNorm (cutoffTraceDefectMaxAtDepth M m · t)
        (ENNReal.ofReal (p + 3 * (t : ℝ) + 3))
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (allOrderDepthProfile M.gamma p t) := by
  let q := p + 3 * (t : ℝ) + 3
  change eLpNorm (cutoffTraceDefectMaxAtDepth M m · t)
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
    ENNReal.ofReal (allOrderDepthProfile M.gamma p t)
  rw [← eLpNorm_ofReal _
    (Filter.Eventually.of_forall (aoPerDepth_depth_max_nonneg M m · t))]
  have hgammaPos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hgamma : M.gamma ≤ 17 / 50000 := by
    simpa only [gammaZero] using hγ
  have hq4 : 4 + 3 * (t : ℝ) ≤ q := by
    dsimp [q]
    linarith
  have hqpos : 0 < q := by linarith [hq4]
  have hqPowPos : 0 < q ^ (64 * M.gamma) := Real.rpow_pos_of_pos hqpos _
  have hbulkProfile := aoPerDepth_bulk_profile_bound
    (γ := M.gamma) (p := p) (t := t) hgammaPos.le hgammaPos hp
  have hbulkProfileAtQ : aoPerDepthTargetCoefficient M.gamma q t *
        (3 : ℝ) ^ (5 * M.gamma * ((t : ℝ) + 1)) ≤
      allOrderDepthProfile M.gamma p t := by
    simpa [q] using hbulkProfile
  have hpow5 : 1 ≤ (3 : ℝ) ^
      (5 * M.gamma * ((t : ℝ) + 1)) :=
    Real.one_le_rpow (by norm_num) (by positivity [M.shellPrefix.gamma_pos])
  have htargetCoeff : 0 ≤ aoPerDepthTargetCoefficient M.gamma q t := by
    dsimp [aoPerDepthTargetCoefficient]
    positivity
  have hP20nat : 20 ≤ smallGammaSeedP M.gamma := by
    dsimp [smallGammaSeedP]
    omega
  have hP20 : 20 ≤ (smallGammaSeedP M.gamma : ℝ) := by exact_mod_cast hP20nat
  by_cases ht0 : t = 0
  · subst t
    by_cases hqP : q ≤ (smallGammaSeedP M.gamma : ℝ)
    · have hcell : ∀ Q : TriadicCube 2,
        Q ∈ descendantsAtDepth (originCube 2 m) 0 →
        eLpNorm (fun ω => ENNReal.ofReal
          (traceDefect (cubeSet Q)
            (Cutoff.coefficientCutoff M.nu m ω).toFun
            (Annealed.sigmaBar M m : ℝ)))
          (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
            ENNReal.ofReal (900000 * M.gamma * (if q < 12 then 12 else q + 2)) := by
        intro Q hQ
        have hQscale : Q.scale = m := by
          have hs := scale_eq_sub_of_mem_descendantsAtDepth hQ
          simpa [originCube] using hs
        exact aoPerDepth_native_cell_bound M h hM hγ hstate m Q hQscale
          (by dsimp [q]; linarith [hp]) hqP
      have hmax := aoPerDepth_max_from_cell_bound M m q
        (900000 * M.gamma * (if q < 12 then 12 else q + 2)) 0
        (by linarith [hqpos]) hcell
      have hmax' : eLpNorm (fun ω =>
          ENNReal.ofReal (cutoffTraceDefectMaxAtDepth M m ω 0))
          (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
            ENNReal.ofReal (900000 * M.gamma * (if q < 12 then 12 else q + 2)) := by
        simpa [Real.rpow_def_of_pos hqpos] using hmax
      have hbudget := aoPerDepth_native_zero_budget
        (γ := M.gamma) (q := q) hgammaPos.le (by dsimp [q]; linarith [hp])
        (mul_nonneg hgammaPos.le hqpos.le)
      have hbudgetPow :
          900000 * M.gamma * (if q < 12 then 12 else q + 2) ≤
            aoPerDepthTargetCoefficient M.gamma q 0 * (3 : ℝ) ^ (5 * M.gamma) := by
        have hpow5zero : 1 ≤ (3 : ℝ) ^ (5 * M.gamma) := by simpa using hpow5
        have hmul := mul_le_mul_of_nonneg_left hpow5zero htargetCoeff
        have hmul' : aoPerDepthTargetCoefficient M.gamma q 0 ≤
            aoPerDepthTargetCoefficient M.gamma q 0 * (3 : ℝ) ^ (5 * M.gamma) := by
          simpa using hmul
        exact hbudget.trans hmul'
      have hfull := ENNReal.ofReal_le_ofReal hbudgetPow
      have hresult := hmax'.trans hfull
      exact hresult.trans
        (ENNReal.ofReal_le_ofReal (by simpa [q] using hbulkProfileAtQ))
    · have hseedGates := aoCir_small_gamma_seed_order_gates (γ := M.gamma) hgammaPos
      have hseed : 1 / 19000 < M.gamma * q := by
        have hstrict : (smallGammaSeedP M.gamma : ℝ) < q := lt_of_not_ge hqP
        exact lt_trans hseedGates.1 (mul_lt_mul_of_pos_left hstrict hgammaPos)
      have hqge20 : 20 ≤ q := by
        have hstrict : (smallGammaSeedP M.gamma : ℝ) < q := lt_of_not_ge hqP
        linarith [hP20]
      have hraw := aoPerDepth_raw_profile_bound reset M h hM hγ hstate m q q
        le_rfl hqge20 0
      by_cases hpow : q ^ (64 * M.gamma) ≤ 10 / 3
      · have hbudget := aoPerDepth_raw_high_tzero_budget hgammaPos.le hseed hqge20 hpow
        have hbound := ENNReal.ofReal_le_ofReal hbudget
        exact (hraw.trans hbound).trans
          (ENNReal.ofReal_le_ofReal (by simpa [q] using hbulkProfileAtQ))
      · have hpow' : 10 / 3 < q ^ (64 * M.gamma) := lt_of_not_ge hpow
        have hbudget := aoPerDepth_raw_high_rare_budget hgammaPos.le hgammaPos hgamma
          hqge20 (by dsimp [q]; linarith [hp]) hpow'
        have hrareProfile := aoPerDepth_rare_profile_bound
          (γ := M.gamma) (p := p) (t := 0) hgammaPos hp
        have hbound := ENNReal.ofReal_le_ofReal hbudget
        exact (hraw.trans hbound).trans (ENNReal.ofReal_le_ofReal hrareProfile)
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht0
    by_cases hq20 : q < 20
    · have ht5 : t ≤ 5 := by
        have htCast : 3 * (t : ℝ) < 16 := by linarith [hq4, hq20]
        have htNat : 3 * t < 16 := by exact_mod_cast htCast
        omega
      by_cases hγsmall : M.gamma ≤ 1 / 327680
      · by_cases hq12 : 12 ≤ q
        · have hwindow : M.gamma * q * ((t : ℝ) + 2) ≤ 1 / 512 := by
            have hq20' : q ≤ 20 := le_of_lt hq20
            have ht7 : (t : ℝ) + 2 ≤ 7 := by
              have htcast : (t : ℝ) ≤ 5 := by exact_mod_cast ht5
              linarith
            have hprod : q * ((t : ℝ) + 2) ≤ 140 := by nlinarith [hq20', ht7]
            have hmul := mul_le_mul_of_nonneg_left hprod
              (show 0 ≤ M.gamma by positivity)
            nlinarith [hγsmall, hmul]
          have hcell : ∀ Q : TriadicCube 2,
              Q ∈ descendantsAtDepth (originCube 2 m) t →
              eLpNorm (fun ω => ENNReal.ofReal
                (traceDefect (cubeSet Q)
                  (Cutoff.coefficientCutoff M.nu m ω).toFun
                  (Annealed.sigmaBar M m : ℝ)))
                (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
                  ENNReal.ofReal
                    ((1017 / 1000 : ℝ) *
                      (900000 * M.gamma * (q + 2) +
                        (t : ℝ) * (19 * q * (9 / 2 : ℝ) * M.gamma *
                          (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120))) +
                      4 * M.gamma * q * (t : ℝ) *
                        (3 : ℝ) ^ (2 * M.gamma * (t : ℝ))) := by
            intro Q hQ
            have hDirect := aoPerDepth_direct_common_frame_cell_bound reset
              M h hM hγ hγsmall hstate m Q t htpos hQ hq12
              (by linarith [hq20, hP20]) hwindow
            apply aoPerDepth_eLp_ofReal_le
              (f := fun ω => traceDefect (cubeSet Q)
                (Cutoff.coefficientCutoff M.nu m ω).toFun
                (Annealed.sigmaBar M m : ℝ))
              (q := q)
              (A := (1017 / 1000 : ℝ) *
                (900000 * M.gamma * (q + 2) +
                  (t : ℝ) * (19 * q * (9 / 2 : ℝ) * M.gamma *
                    (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120))) +
                4 * M.gamma * q * (t : ℝ) *
                  (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)))
              hDirect.1
              (by intro ω; exact aoPerDepth_trace_nonneg_at M m Q ω)
              hDirect.2
          have hmax := aoPerDepth_max_from_cell_bound M m q _ t
            (by linarith [hq12]) hcell
          let F := (3 : ℝ) ^ (2 * M.gamma * (t : ℝ))
          have hframe : F ≤ 10008 / 10000 := by
            dsimp [F]
            have htgamma : M.gamma * (t : ℝ) ≤ gammaZero := by
              have htcast : (t : ℝ) ≤ 5 := by exact_mod_cast ht5
              have hmul := mul_le_mul_of_nonneg_right htcast
                (show 0 ≤ M.gamma by positivity)
              have hsmall' : M.gamma * 5 ≤ 1 / 32768 := by nlinarith [hγsmall]
              have hsmall'' : 5 * M.gamma ≤ 1 / 32768 := by
                calc
                  5 * M.gamma = M.gamma * 5 := by ring
                  _ ≤ 1 / 32768 := hsmall'
              have htgamma' : M.gamma * (t : ℝ) ≤ 1 / 32768 := by
                calc
                  M.gamma * (t : ℝ) = (t : ℝ) * M.gamma := by ring
                  _ ≤ 5 * M.gamma := hmul
                  _ ≤ 1 / 32768 := hsmall''
              have hgammaGate : (1 / 32768 : ℝ) ≤ gammaZero := by
                norm_num [gammaZero]
              exact htgamma'.trans hgammaGate
            have hgate := Numerics.AllOrder.allorder_frame_gates
            have hexp : 2 * M.gamma * (t : ℝ) ≤ 2 * gammaZero := by
              nlinarith [M.shellPrefix.gamma_pos.le, htgamma]
            have hpow := Real.rpow_le_rpow_of_exponent_le
              (by norm_num : (1 : ℝ) ≤ 3) hexp
            have hzeroOld : (3 : ℝ) ^ (2 * gammaZero) < 1.0008 :=
              hgate.2.2.2.1.trans_lt hgate.2.2.2.2.1
            have hzero : (3 : ℝ) ^ (2 * gammaZero) < 10008 / 10000 := by
              have hrat : (1.0008 : ℝ) = 10008 / 10000 := by norm_num
              simpa [hrat] using hzeroOld
            exact hpow.trans hzero.le
          have hbudget := aoPerDepth_direct_budget (γ := M.gamma) (q := q)
            hgammaPos.le htpos hq4 hframe
          have hmaxScalar : eLpNorm (fun ω =>
              ENNReal.ofReal (cutoffTraceDefectMaxAtDepth M m ω t))
              (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
                ENNReal.ofReal (aoPerDepthTargetCoefficient M.gamma q t) := by
            exact hmax.trans (aoPerDepth_ofReal_product_le
              (Real.rpow_nonneg (by norm_num) _) hbudget)
          have hpow5t : 1 ≤ (3 : ℝ) ^
              (5 * M.gamma * ((t : ℝ) + 1)) :=
            Real.one_le_rpow (by norm_num) (by positivity [M.shellPrefix.gamma_pos])
          have hbudgetPow := le_mul_of_one_le_right htargetCoeff hpow5t
          exact (hmaxScalar.trans (ENNReal.ofReal_le_ofReal hbudgetPow)).trans
            (ENNReal.ofReal_le_ofReal (by simpa [q] using hbulkProfileAtQ))
        · have hqLt12 : q < 12 := lt_of_not_ge hq12
          have ht2 : t ≤ 2 := by
            have htCast : 3 * (t : ℝ) < 8 := by linarith [hq4, hqLt12]
            have htNat : 3 * t < 8 := by exact_mod_cast htCast
            omega
          have hwindow : M.gamma * 12 * ((t : ℝ) + 2) ≤ 1 / 512 := by
            have ht4 : (t : ℝ) + 2 ≤ 4 := by
              have htcast : (t : ℝ) ≤ 2 := by exact_mod_cast ht2
              linarith
            have hprod : (12 : ℝ) * ((t : ℝ) + 2) ≤ 48 := by nlinarith [ht4]
            have hmul := mul_le_mul_of_nonneg_left hprod
              (show 0 ≤ M.gamma by positivity)
            nlinarith [hγsmall, hmul]
          have hq12depth : 4 + 3 * (t : ℝ) ≤ 12 := by
            have htcast : (t : ℝ) ≤ 2 := by exact_mod_cast ht2
            nlinarith
          have hcell : ∀ Q : TriadicCube 2,
              Q ∈ descendantsAtDepth (originCube 2 m) t →
              eLpNorm (fun ω => ENNReal.ofReal
                (traceDefect (cubeSet Q)
                  (Cutoff.coefficientCutoff M.nu m ω).toFun
                  (Annealed.sigmaBar M m : ℝ)))
                (ENNReal.ofReal 12) (Cutoff.cutoffSampleLaw M).toMeasure ≤
                  ENNReal.ofReal
                    ((1017 / 1000 : ℝ) *
                      (900000 * M.gamma * (12 + 2) +
                        (t : ℝ) * (19 * 12 * (9 / 2 : ℝ) * M.gamma *
                          (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120))) +
                      4 * M.gamma * 12 * (t : ℝ) *
                        (3 : ℝ) ^ (2 * M.gamma * (t : ℝ))) := by
            intro Q hQ
            have hDirect := aoPerDepth_direct_common_frame_cell_bound reset
              M h hM hγ hγsmall hstate m Q t htpos hQ
              (by norm_num : 12 ≤ (12 : ℝ))
              (by have hP : 20 ≤ (smallGammaSeedP M.gamma : ℝ) := hP20
                  linarith) hwindow
            apply aoPerDepth_eLp_ofReal_le
              (f := fun ω => traceDefect (cubeSet Q)
                (Cutoff.coefficientCutoff M.nu m ω).toFun
                (Annealed.sigmaBar M m : ℝ))
              (q := 12)
              (A := (1017 / 1000 : ℝ) *
                (900000 * M.gamma * (12 + 2) +
                  (t : ℝ) * (19 * 12 * (9 / 2 : ℝ) * M.gamma *
                    (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120))) +
                4 * M.gamma * 12 * (t : ℝ) *
                  (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)))
              hDirect.1
              (by intro ω; exact aoPerDepth_trace_nonneg_at M m Q ω)
              hDirect.2
          have hmax := aoPerDepth_max_from_cell_bound M m 12 _ t
            (by norm_num) hcell
          have hframe : (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) ≤ 10008 / 10000 := by
            have htcast : (t : ℝ) ≤ 2 := by exact_mod_cast ht2
            have hsmall' : M.gamma * (t : ℝ) ≤ 2 / 327680 := by
              have hmul := mul_le_mul_of_nonneg_right htcast
                (show 0 ≤ M.gamma by positivity)
              nlinarith [hγsmall, hmul]
            have hsmall'' : M.gamma * (t : ℝ) ≤ gammaZero := by
              exact hsmall'.trans (by norm_num [gammaZero])
            have hgate := Numerics.AllOrder.allorder_frame_gates
            have hexp : 2 * M.gamma * (t : ℝ) ≤ 2 * gammaZero := by
              nlinarith [M.shellPrefix.gamma_pos.le, hsmall'']
            have hpow := Real.rpow_le_rpow_of_exponent_le
              (by norm_num : (1 : ℝ) ≤ 3) hexp
            have hzeroOld : (3 : ℝ) ^ (2 * gammaZero) < 1.0008 :=
              hgate.2.2.2.1.trans_lt hgate.2.2.2.2.1
            have hzero : (3 : ℝ) ^ (2 * gammaZero) < 10008 / 10000 := by
              have hrat : (1.0008 : ℝ) = 10008 / 10000 := by norm_num
              simpa [hrat] using hzeroOld
            exact hpow.trans hzero.le
          have hbudget := aoPerDepth_direct_twelve_budget (γ := M.gamma) (q := q)
            hgammaPos.le htpos ht2 hq4 hframe
          have hpop : Real.rpow 9 ((t : ℝ) / 12) ≤ 21 / 10 :=
            aoPerDepth_population_le hq12depth
          have hmaxScalar : eLpNorm (fun ω =>
              ENNReal.ofReal (cutoffTraceDefectMaxAtDepth M m ω t))
              (ENNReal.ofReal 12) (Cutoff.cutoffSampleLaw M).toMeasure ≤
                ENNReal.ofReal (aoPerDepthTargetCoefficient M.gamma q t) := by
            exact hmax.trans (aoPerDepth_ofReal_product_le
              (Real.rpow_nonneg (by norm_num) _) hbudget)
          have hmono : eLpNorm (fun ω =>
              ENNReal.ofReal (cutoffTraceDefectMaxAtDepth M m ω t))
              (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
            eLpNorm (fun ω =>
              ENNReal.ofReal (cutoffTraceDefectMaxAtDepth M m ω t))
              (ENNReal.ofReal 12) (Cutoff.cutoffSampleLaw M).toMeasure := by
            exact eLpNorm_le_eLpNorm_of_exponent_le
              (p := ENNReal.ofReal q) (q := ENNReal.ofReal 12)
              (ENNReal.ofReal_le_ofReal (le_of_lt hqLt12))
          have hmaxQ := hmono.trans hmaxScalar
          have hpow5t : 1 ≤ (3 : ℝ) ^
              (5 * M.gamma * ((t : ℝ) + 1)) :=
            Real.one_le_rpow (by norm_num) (by positivity [M.shellPrefix.gamma_pos])
          have hbudgetPow := le_mul_of_one_le_right htargetCoeff hpow5t
          exact (hmaxQ.trans (ENNReal.ofReal_le_ofReal hbudgetPow)).trans
            (ENNReal.ofReal_le_ofReal (by simpa [q] using hbulkProfileAtQ))
      · have hγlower : 1 / 327680 < M.gamma := lt_of_not_ge hγsmall
        have hraw := aoPerDepth_raw_profile_bound reset M h hM hγ hstate m q 20
          (by linarith [hq20]) (by norm_num) t
        have hbudget := aoPerDepth_raw_low_budget hgammaPos.le hγlower hgamma
          hq4 hq20 htpos
        have hbound := ENNReal.ofReal_le_ofReal hbudget
        exact (hraw.trans hbound).trans
          (ENNReal.ofReal_le_ofReal (by simpa [q] using hbulkProfileAtQ))
    · have hqge20 : 20 ≤ q := le_of_not_gt hq20
      by_cases hγsmall : M.gamma ≤ 1 / 327680
      · by_cases hdirect : q ≤ (smallGammaSeedP M.gamma : ℝ) ∧
            M.gamma * q * ((t : ℝ) + 2) ≤ 1 / 512
        · rcases hdirect with ⟨hqP, hwindow⟩
          have hcell : ∀ Q : TriadicCube 2,
            Q ∈ descendantsAtDepth (originCube 2 m) t →
            eLpNorm (fun ω => ENNReal.ofReal
              (traceDefect (cubeSet Q)
                (Cutoff.coefficientCutoff M.nu m ω).toFun
                (Annealed.sigmaBar M m : ℝ)))
              (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
                ENNReal.ofReal
                  ((1017 / 1000 : ℝ) *
                    (900000 * M.gamma * (q + 2) +
                      (t : ℝ) * (19 * q * (9 / 2 : ℝ) * M.gamma *
                        (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120))) +
                    4 * M.gamma * q * (t : ℝ) *
                      (3 : ℝ) ^ (2 * M.gamma * (t : ℝ))) := by
            intro Q hQ
            have hDirect := aoPerDepth_direct_common_frame_cell_bound reset
              M h hM hγ hγsmall hstate m Q t htpos hQ
              (by linarith [hqge20]) hqP hwindow
            apply aoPerDepth_eLp_ofReal_le
              (f := fun ω => traceDefect (cubeSet Q)
                (Cutoff.coefficientCutoff M.nu m ω).toFun
                (Annealed.sigmaBar M m : ℝ))
              (q := q)
              (A := (1017 / 1000 : ℝ) *
                (900000 * M.gamma * (q + 2) +
                  (t : ℝ) * (19 * q * (9 / 2 : ℝ) * M.gamma *
                    (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120))) +
                4 * M.gamma * q * (t : ℝ) *
                  (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)))
              hDirect.1
              (by intro ω; exact aoPerDepth_trace_nonneg_at M m Q ω)
              hDirect.2
          have hmax := aoPerDepth_max_from_cell_bound M m q _ t
            (by linarith [hqge20]) hcell
          let F := (3 : ℝ) ^ (2 * M.gamma * (t : ℝ))
          have hframe : F ≤ 10008 / 10000 := by
            dsimp [F]
            have hgammaT : M.gamma * (t : ℝ) ≤ 1 / 6144 := by
              have hqnonneg : 0 ≤ q := le_trans (by norm_num) hqge20
              have hmul := mul_le_mul_of_nonneg_right
                (show (12 : ℝ) ≤ q by linarith [hqge20])
                (mul_nonneg M.shellPrefix.gamma_pos.le hqnonneg)
              nlinarith [hwindow]
            have hgammaT0 : M.gamma * (t : ℝ) ≤ gammaZero := by
              exact hgammaT.trans (by norm_num [gammaZero])
            have hgate := Numerics.AllOrder.allorder_frame_gates
            have hexp : 2 * M.gamma * (t : ℝ) ≤ 2 * gammaZero := by
              nlinarith [M.shellPrefix.gamma_pos.le, hgammaT0]
            have hpow := Real.rpow_le_rpow_of_exponent_le
              (by norm_num : (1 : ℝ) ≤ 3) hexp
            have hzeroOld : (3 : ℝ) ^ (2 * gammaZero) < 1.0008 :=
              hgate.2.2.2.1.trans_lt hgate.2.2.2.2.1
            have hzero : (3 : ℝ) ^ (2 * gammaZero) < 10008 / 10000 := by
              have hrat : (1.0008 : ℝ) = 10008 / 10000 := by norm_num
              simpa [hrat] using hzeroOld
            exact hpow.trans hzero.le
          have hbudget := aoPerDepth_direct_budget (γ := M.gamma) (q := q)
            hgammaPos.le htpos hq4 hframe
          have hmaxScalar : eLpNorm (fun ω =>
              ENNReal.ofReal (cutoffTraceDefectMaxAtDepth M m ω t))
              (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
                ENNReal.ofReal
                  (aoPerDepthTargetCoefficient M.gamma q t) := by
            exact hmax.trans (aoPerDepth_ofReal_product_le
              (Real.rpow_nonneg (by norm_num) _) hbudget)
          have hpow5t : 1 ≤ (3 : ℝ) ^
              (5 * M.gamma * ((t : ℝ) + 1)) :=
            Real.one_le_rpow (by norm_num) (by positivity [M.shellPrefix.gamma_pos])
          have hbudgetPow : aoPerDepthTargetCoefficient M.gamma q t ≤
              aoPerDepthTargetCoefficient M.gamma q t *
                (3 : ℝ) ^ (5 * M.gamma * ((t : ℝ) + 1)) :=
            le_mul_of_one_le_right htargetCoeff hpow5t
          have hresult := hmaxScalar.trans (ENNReal.ofReal_le_ofReal hbudgetPow)
          exact hresult.trans
            (ENNReal.ofReal_le_ofReal (by simpa [q] using hbulkProfileAtQ))
        · have hseed : 1 / 19000 < M.gamma * q ∨
              1 / 1536 < M.gamma * q * (t : ℝ) := by
            by_cases hqP : q ≤ (smallGammaSeedP M.gamma : ℝ)
            · right
              have hnotwindow : ¬ M.gamma * q * ((t : ℝ) + 2) ≤ 1 / 512 := by
                intro hwin
                exact hdirect ⟨hqP, hwin⟩
              have hnot : 1 / 512 < M.gamma * q * ((t : ℝ) + 2) :=
                lt_of_not_ge hnotwindow
              have htBound : (t : ℝ) + 2 ≤ 3 * (t : ℝ) := by
                have ht1 : 1 ≤ (t : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt htpos))
                nlinarith
              have hmul := mul_le_mul_of_nonneg_left htBound
                (mul_nonneg M.shellPrefix.gamma_pos.le
                  (le_trans (by norm_num) hqge20))
              nlinarith [hnot, hmul]
            · left
              have hseedGates := aoCir_small_gamma_seed_order_gates (γ := M.gamma) hgammaPos
              have hstrict : (smallGammaSeedP M.gamma : ℝ) < q := lt_of_not_ge hqP
              have hseedP := lt_trans hseedGates.1
                (mul_lt_mul_of_pos_left hstrict hgammaPos)
              exact hseedP
          have hraw := aoPerDepth_raw_profile_bound reset M h hM hγ hstate m q q
            le_rfl hqge20 t
          by_cases hpow : q ^ (64 * M.gamma) ≤ 10 / 3
          · have hbudget := aoPerDepth_raw_high_positive_budget hgammaPos.le htpos hseed
              hqge20 hq4 hpow
            have hbound := ENNReal.ofReal_le_ofReal hbudget
            exact (hraw.trans hbound).trans
              (ENNReal.ofReal_le_ofReal (by simpa [q] using hbulkProfileAtQ))
          · have hpow' : 10 / 3 < q ^ (64 * M.gamma) := lt_of_not_ge hpow
            have hbudget := aoPerDepth_raw_high_rare_budget hgammaPos.le hgammaPos hgamma
              hqge20 hq4 hpow'
            have hrareProfile := aoPerDepth_rare_profile_bound
              (γ := M.gamma) (p := p) (t := t) hgammaPos hp
            have hbound := ENNReal.ofReal_le_ofReal hbudget
            exact (hraw.trans hbound).trans (ENNReal.ofReal_le_ofReal hrareProfile)
      · have hraw := aoPerDepth_raw_profile_bound reset M h hM hγ hstate m q q
          le_rfl hqge20 t
        by_cases hpow : q ^ (64 * M.gamma) ≤ 10 / 3
        · have hseedGates := aoCir_small_gamma_seed_order_gates (γ := M.gamma) hgammaPos
          have hseed : 1 / 19000 < M.gamma * q := by
            have hP20strict : (smallGammaSeedP M.gamma : ℝ) = 20 := by
              have hγlower : (1 / 327680 : ℝ) < M.gamma := lt_of_not_ge hγsmall
              have hPnat := aoCir_large_gamma_cutoff_eq_twenty hγlower
              exact_mod_cast hPnat
            have hPq : (smallGammaSeedP M.gamma : ℝ) ≤ q := by
              rw [hP20strict]
              exact_mod_cast hqge20
            exact lt_of_lt_of_le hseedGates.1
              (mul_le_mul_of_nonneg_left hPq hgammaPos.le)
          have hbudget := aoPerDepth_raw_high_positive_budget hgammaPos.le htpos
            (Or.inl hseed) hqge20 hq4 hpow
          have hbound := ENNReal.ofReal_le_ofReal hbudget
          exact (hraw.trans hbound).trans
            (ENNReal.ofReal_le_ofReal (by simpa [q] using hbulkProfileAtQ))
        · have hpow' : 10 / 3 < q ^ (64 * M.gamma) := lt_of_not_ge hpow
          have hbudget := aoPerDepth_raw_high_rare_budget hgammaPos.le hgammaPos hgamma
            hqge20 hq4 hpow'
          have hbound := ENNReal.ofReal_le_ofReal hbudget
          have hrareProfile := aoPerDepth_rare_profile_bound
            (γ := M.gamma) (p := p) (t := t) hgammaPos hp
          exact (hraw.trans hbound).trans (ENNReal.ofReal_le_ofReal hrareProfile)

/-- AO-PER-DEPTH. The order-reset producer is instantiated internally. -/
theorem ao_per_depth
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    (m : ℤ) {p : ℝ} (hp : 1 ≤ p) (t : ℕ) :
    eLpNorm (cutoffTraceDefectMaxAtDepth M m · t)
        (ENNReal.ofReal (p + 3 * (t : ℝ) + 3))
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (allOrderDepthProfile M.gamma p t) := by
  exact ao_per_depth_of_reset order_reset_producer M h hM hγ hstate m hp t

end ASDExplicitGamma.AllOrder
