module

public import ASDExplicitGamma.Main.EnvelopeA
public import ASDExplicitGamma.Native.OldSignedMeanSourceTransport
public import ASDExplicitGamma.Native.SourceChainRows

/-! MA-ENVELOPE-A, using the exact fifth source row and the
sharp fixed-depth OLD source-slope comparison. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Native ASDExplicitGamma.Inverse
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Variational

private theorem main_pa_sum_sq_lower {v : ℝ} (hv : 0 ≤ v) :
    (221 / 1000000 : ℝ) * v ≤
      (mainPa v 0 + mainPa v 1 + mainPa v 2) ^ 2 := by
  have h0rad : ((383 / 100000 : ℝ) * Real.sqrt v) ^ 2 ≤
      (39 / 5 : ℝ) * mainA2 v := by
    rw [mainA2, mul_pow, Real.sq_sqrt hv]
    have hcoeff : (383 / 100000 : ℝ) ^ 2 ≤
        (39 / 5 : ℝ) * (3 : ℝ) ^ (-12 : ℤ) := by norm_num
    nlinarith [mul_nonneg hv (sub_nonneg.mpr hcoeff)]
  have h0rad' : (383 / 100000 : ℝ) * Real.sqrt v ≤
      Real.sqrt ((39 / 5 : ℝ) * mainA2 v) :=
    Real.le_sqrt_of_sq_le h0rad
  have h1rad : ((766 / 100000 : ℝ) * Real.sqrt v) ^ 2 ≤
      (156 / 5 : ℝ) * mainA2 v := by
    rw [mainA2, mul_pow, Real.sq_sqrt hv]
    have hcoeff : (766 / 100000 : ℝ) ^ 2 ≤
        (156 / 5 : ℝ) * (3 : ℝ) ^ (-12 : ℤ) := by norm_num
    nlinarith [mul_nonneg hv (sub_nonneg.mpr hcoeff)]
  have h1rad' : (766 / 100000 : ℝ) * Real.sqrt v ≤
      Real.sqrt ((156 / 5 : ℝ) * mainA2 v) :=
    Real.le_sqrt_of_sq_le h1rad
  have h2rad : ((81 / 1000000 : ℝ) * Real.sqrt v) ^ 2 ≤
      (46488 / 25 : ℝ) * mainA4 v := by
    rw [mainA4, mul_pow, Real.sq_sqrt hv]
    have hcoeff : (81 / 1000000 : ℝ) ^ 2 ≤
        (46488 / 25 : ℝ) * (3 : ℝ) ^ (-24 : ℤ) := by norm_num
    nlinarith [mul_nonneg hv (sub_nonneg.mpr hcoeff)]
  have h2rad' : (81 / 1000000 : ℝ) * Real.sqrt v ≤
      Real.sqrt ((46488 / 25 : ℝ) * mainA4 v) :=
    Real.le_sqrt_of_sq_le h2rad
  have hpa0 : (383 / 100000 : ℝ) * Real.sqrt v ≤ mainPa v 0 := by
    simpa [mainPa] using h0rad'
  have hpa1 : (1103 / 100000 : ℝ) * Real.sqrt v ≤ mainPa v 1 := by
    have houter : (1103 / 100000 : ℝ) ≤
        (36 / 25 : ℝ) * (766 / 100000 : ℝ) := by norm_num
    have hscaled : (1103 / 100000 : ℝ) * Real.sqrt v ≤
        (36 / 25 : ℝ) * (766 / 100000 : ℝ) * Real.sqrt v := by
      nlinarith [houter, Real.sqrt_nonneg v]
    calc
      _ ≤ (36 / 25 : ℝ) * ((766 / 100000 : ℝ) * Real.sqrt v) := by
        nlinarith only [hscaled]
      _ ≤ (36 / 25 : ℝ) *
          Real.sqrt ((156 / 5 : ℝ) * mainA2 v) :=
        mul_le_mul_of_nonneg_left h1rad' (by norm_num)
      _ = mainPa v 1 := by simp [mainPa]
  have hpa2 : (23 / 1000000 : ℝ) * Real.sqrt v ≤ mainPa v 2 := by
    have houter : (23 / 1000000 : ℝ) ≤
        (57 / 200 : ℝ) * (81 / 1000000 : ℝ) := by norm_num
    have hscaled : (23 / 1000000 : ℝ) * Real.sqrt v ≤
        (57 / 200 : ℝ) * (81 / 1000000 : ℝ) * Real.sqrt v := by
      nlinarith [houter, Real.sqrt_nonneg v]
    calc
      _ ≤ (57 / 200 : ℝ) * ((81 / 1000000 : ℝ) * Real.sqrt v) := by
        nlinarith only [hscaled]
      _ ≤ (57 / 200 : ℝ) *
          Real.sqrt ((46488 / 25 : ℝ) * mainA4 v) :=
        mul_le_mul_of_nonneg_left h2rad' (by norm_num)
      _ = mainPa v 2 := by simp [mainPa]
  have hsum : (14883 / 1000000 : ℝ) * Real.sqrt v ≤
      mainPa v 0 + mainPa v 1 + mainPa v 2 := by
    have hcoeff : (14883 / 1000000 : ℝ) =
        (383 / 100000 : ℝ) + 1103 / 100000 + 23 / 1000000 := by norm_num
    rw [hcoeff]
    linarith only [hpa0, hpa1, hpa2]
  have hsum_nonneg : 0 ≤ mainPa v 0 + mainPa v 1 + mainPa v 2 := by
    simp [mainPa]
    positivity
  have hlower_nonneg : 0 ≤ (14883 / 1000000 : ℝ) * Real.sqrt v :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hdiff_nonneg : 0 ≤
      mainPa v 0 + mainPa v 1 + mainPa v 2 -
        (14883 / 1000000 : ℝ) * Real.sqrt v := sub_nonneg.mpr hsum
  have hsumPlus : 0 ≤
      mainPa v 0 + mainPa v 1 + mainPa v 2 +
        (14883 / 1000000 : ℝ) * Real.sqrt v :=
    add_nonneg hsum_nonneg hlower_nonneg
  have hsquare : ((14883 / 1000000 : ℝ) * Real.sqrt v) ^ 2 ≤
      (mainPa v 0 + mainPa v 1 + mainPa v 2) ^ 2 := by
    have hprod := mul_nonneg hdiff_nonneg hsumPlus
    nlinarith only [hprod]
  calc
    (221 / 1000000 : ℝ) * v ≤
        ((14883 / 1000000 : ℝ) * Real.sqrt v) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hv]
      nlinarith
    _ ≤ (mainPa v 0 + mainPa v 1 + mainPa v 2) ^ 2 := hsquare

private theorem main_kf_lower {v : ℝ} (hv : 0 ≤ v) :
    (48 / 1000000 : ℝ) * v ≤ mainKf v := by
  have hsqrtLo : (141 / 100 : ℝ) ≤ Real.sqrt 2 := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hsqrtHi : Real.sqrt 2 ≤ (10 / 7 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hinv : (7 / 10 : ℝ) ≤ (Real.sqrt 2)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (Real.sqrt_pos.2 (by norm_num))]
    nlinarith only [hsqrtHi]
  have hsecond : (1008 / 1000 : ℝ) ≤ (36 / 25 : ℝ) / Real.sqrt 2 := by
    have hh := mul_le_mul_of_nonneg_left hinv
      (by norm_num : (0 : ℝ) ≤ 36 / 25)
    calc
      (1008 / 1000 : ℝ) = (36 / 25) * (7 / 10) := by norm_num
      _ ≤ (36 / 25) * (Real.sqrt 2)⁻¹ := hh
      _ = (36 / 25) / Real.sqrt 2 := by
        exact (div_eq_mul_inv _ _).symm
  have hbracket : (1657 / 1000 : ℝ) ≤
      1 / 4 + (36 / 25) / Real.sqrt 2 + (57 / 200) * Real.sqrt 2 := by
    nlinarith only [hsecond, hsqrtLo]
  have hpow : (3 : ℝ) ^ (-12 : ℤ) = 1 / 531441 := by norm_num
  have hcoeff : (48 / 1000000 : ℝ) ≤
      (78 / 5 : ℝ) * (1 / 531441) * (1657 / 1000) := by norm_num
  unfold mainKf mainA2
  rw [hpow]
  calc
    (48 / 1000000 : ℝ) * v ≤
        ((78 / 5 : ℝ) * (1 / 531441) * (1657 / 1000)) * v :=
      mul_le_mul_of_nonneg_right hcoeff hv
    _ ≤ ((78 / 5 : ℝ) * (1 / 531441) *
        (1 / 4 + (36 / 25) / Real.sqrt 2 + (57 / 200) * Real.sqrt 2)) * v := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbracket (by positivity)) hv
    _ = (78 / 5 : ℝ) * (v * (1 / 531441)) *
        (1 / 4 + (36 / 25) / Real.sqrt 2 + (57 / 200) * Real.sqrt 2) := by ring

private theorem main_mu_g9_lower {v gamma : ℝ}
    (hv : 0 ≤ v) (hγ : 0 ≤ gamma) :
    v * (2 * mainBetaOld + (107 / 100000 : ℝ) * 4 *
        mainRawA gamma * (3 : ℝ) ^ (26 * gamma)) ≤ mainMu v gamma := by
  have hpa := main_pa_sum_sq_lower hv
  have hkf := main_kf_lower hv
  have hbeta0 : 0 ≤ mainBetaOld := by norm_num [mainBetaOld]
  have hApos : 0 ≤ mainRawA gamma := by
    unfold mainRawA
    positivity
  have hpowpos : 0 ≤ (3 : ℝ) ^ (26 * gamma) :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hrawWeight : 0 ≤ 4 * mainRawA gamma *
      (3 : ℝ) ^ (26 * gamma) :=
    mul_nonneg (mul_nonneg (by norm_num) hApos) hpowpos
  have hKf0 : 0 ≤ mainKf v :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 48 / 1000000) hv).trans hkf
  have hJtail : 0 ≤ 52 * v * Real.sqrt 3 * mainBetaOld ^ 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hv)
      (Real.sqrt_nonneg _)) (pow_nonneg hbeta0 _)
  have hKtail : 0 ≤ 52 * v * Real.sqrt 3 * mainBetaOld ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hv)
      (Real.sqrt_nonneg _)) (pow_nonneg hbeta0 _)
  have hJbase :
      (26 / 25 : ℝ) * mainBetaOld ^ 2 * mainRawFactor gamma *
        mainRawA gamma ≤ mainJ0 v gamma := by
    unfold mainJ0
    exact le_add_of_nonneg_right hJtail
  have hKbase :
      (26 / 25 : ℝ) * mainBetaOld * mainRawFactor gamma *
        mainRawA gamma ≤ mainK0 v gamma := by
    unfold mainK0
    exact le_add_of_nonneg_right hKtail
  have hJterm :
      v * ((221 / 1000000 : ℝ) * (232 / 125) *
          ((26 / 25 : ℝ) * mainBetaOld ^ 2) *
          (4 * mainRawA gamma * (3 : ℝ) ^ (26 * gamma))) ≤
        (232 / 125 : ℝ) *
          (mainPa v 0 + mainPa v 1 + mainPa v 2) ^ 2 * mainJ0 v gamma := by
    have hcoeff : 0 ≤ (232 / 125 : ℝ) *
        ((26 / 25 : ℝ) * mainBetaOld ^ 2) *
        (4 * mainRawA gamma * (3 : ℝ) ^ (26 * gamma)) := by
      exact mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 232 / 125)
          (mul_nonneg (by norm_num) (sq_nonneg mainBetaOld))) hrawWeight
    have h1 := mul_le_mul_of_nonneg_right hpa hcoeff
    have h2 := mul_le_mul_of_nonneg_left hJbase
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 232 / 125)
        (sq_nonneg (mainPa v 0 + mainPa v 1 + mainPa v 2)))
    have hfactorEq : mainRawFactor gamma =
        4 * (3 : ℝ) ^ (26 * gamma) := by rfl
    rw [hfactorEq] at h2
    nlinarith only [h1, h2]
  have hKterm :
      v * (2 * (48 / 1000000 : ℝ) *
          ((26 / 25 : ℝ) * mainBetaOld) *
          (4 * mainRawA gamma * (3 : ℝ) ^ (26 * gamma))) ≤
        2 * mainKf v * mainK0 v gamma := by
    have hcoeff : 0 ≤ 2 * ((26 / 25 : ℝ) * mainBetaOld) *
        (4 * mainRawA gamma * (3 : ℝ) ^ (26 * gamma)) := by
      exact mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 26 / 25) hbeta0))
        hrawWeight
    have h1 := mul_le_mul_of_nonneg_right hkf hcoeff
    have h2 := mul_le_mul_of_nonneg_left hKbase
      (show 0 ≤ 2 * mainKf v from mul_nonneg (by norm_num) hKf0)
    have hfactorEq : mainRawFactor gamma =
        4 * (3 : ℝ) ^ (26 * gamma) := by rfl
    rw [hfactorEq] at h2
    nlinarith only [h1, h2]
  have hcoeff :
      (107 / 100000 : ℝ) ≤
        (221 / 1000000 : ℝ) * (232 / 125) *
            ((26 / 25 : ℝ) * mainBetaOld ^ 2) +
          2 * (48 / 1000000 : ℝ) * ((26 / 25 : ℝ) * mainBetaOld) := by
    norm_num [mainBetaOld]
  have hterms :
      v * ((107 / 100000 : ℝ) *
          (4 * mainRawA gamma * (3 : ℝ) ^ (26 * gamma))) ≤
        (232 / 125 : ℝ) *
            (mainPa v 0 + mainPa v 1 + mainPa v 2) ^ 2 * mainJ0 v gamma +
          2 * mainKf v * mainK0 v gamma := by
    have hcommon : 0 ≤ v *
        (4 * mainRawA gamma * (3 : ℝ) ^ (26 * gamma)) := by
      exact mul_nonneg hv hrawWeight
    have hc := mul_le_mul_of_nonneg_left hcoeff hcommon
    rw [mul_add] at hc
    have hsum := add_le_add hJterm hKterm
    nlinarith only [hc, hsum]
  unfold mainMu
  have hbase : v * (2 * mainBetaOld) ≤
      2 * v * (mainBetaOld + Real.sqrt 3 * mainEpsOld) := by
    have heps : 0 ≤ Real.sqrt 3 * mainEpsOld :=
      mul_nonneg (Real.sqrt_nonneg _) (by norm_num [mainEpsOld])
    nlinarith only [mul_nonneg hv heps]
  nlinarith only [hterms, hbase]

private theorem old_signed_mean_cap_scalar_le {gamma v : ℝ}
    (hv : 0 ≤ v) (hγ : 0 ≤ gamma) (hγ0 : gamma ≤ gammaZero) :
    v * (3 : ℝ) ^ (10 * gamma) *
        (2 * (3683 / 2500 : ℝ) +
          2 * lemmaVH2kn (1 / 729) (1 / 729) *
            (3683 / 2500 : ℝ) *
            oldSignedP20Full64Cap gamma 6 +
          (3 : ℝ) ^ (10 * gamma) *
            pureFluxCovarianceMu
              (pureFluxCovarianceA 0 5) (pureFluxCovarianceB 0 5) *
            (3683 / 2500 : ℝ) ^ 2 * oldSignedP20Full64Cap gamma 6) ≤
      v * (2 * (3683 / 2500 : ℝ) * (1 + 12 * gamma) +
        4 * (10668 / 10000000 : ℝ) * mainRawA gamma *
          (3 : ℝ) ^ (26 * gamma)) := by
  let C : ℝ := (3 : ℝ) ^ (10 * gamma)
  let x : ℝ := (3 : ℝ) ^ (26 * gamma)
  let Aold : ℝ := (2018618 / 1000000 : ℝ) +
    gamma * (16684 * 7 + 5899542)
  have hCone : 1 ≤ C := by
    dsimp [C]
    exact Real.one_le_rpow (by norm_num) (mul_nonneg (by norm_num) hγ)
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hx2 : x ^ 2 ≤ 21 / 20 := by
    have hexp : 52 * gamma ≤ 52 * gammaZero := by nlinarith
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
    have hp0 := ASDExplicitGamma.Numerics.Inverse.inv_three_power_bound
      (52 * gammaZero) (by norm_num [gammaZero]) (by norm_num [gammaZero])
    have hpow : x ^ 2 = (3 : ℝ) ^ (52 * gamma) := by
      dsimp [x]
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    rw [hpow]
    exact hp.trans (hp0.trans (by norm_num [gammaZero]))
  have hCleX : C ≤ x := by
    dsimp [C, x]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    nlinarith [hγ]
  have hCsq : C ^ 2 ≤ x ^ 2 := by
    have hp : 0 ≤ (x - C) * (x + C) :=
      mul_nonneg (sub_nonneg.mpr hCleX) (by positivity)
    nlinarith only [hp]
  have hCup : C ≤ 1 + 12 * gamma := by
    have hp := ASDExplicitGamma.Numerics.Inverse.inv_three_power_bound
      (10 * gamma) (by positivity) (by norm_num [gammaZero] at hγ0 ⊢; nlinarith)
    have hden : 0 < 1 - 11 * gamma := by
      norm_num [gammaZero] at hγ0 ⊢
      nlinarith [hγ]
    have hfrac : 1 / (1 - 11 * gamma) ≤ 1 + 12 * gamma := by
      rw [div_le_iff₀ hden]
      have hgsmall : gamma ≤ 1 / 132 := by
        norm_num [gammaZero] at hγ0 ⊢
        linarith
      have hquad : 132 * gamma ^ 2 ≤ gamma := by
        nlinarith [mul_nonneg hγ (sub_nonneg.mpr hgsmall)]
      nlinarith only [hquad]
    have hp' : C ≤ 1 / (1 - 11 * gamma) := by
      dsimp [C]
      convert hp using 1 <;> ring
    exact hp'.trans hfrac
  have hAold : Aold ≤ mainRawA gamma := by
    dsimp [Aold, mainRawA]
    nlinarith [hγ]
  have hF : oldSignedP20Full64Cap gamma 6 = 4 * Aold * x := by
    dsimp [Aold, x, oldSignedP20Full64Cap]
    rw [show 2 * gamma * 7 + 2 * gamma * 6 = 26 * gamma by ring]
  have hκ : 0 ≤ lemmaVH2kn (1 / 729) (1 / 729) ∧
      lemmaVH2kn (1 / 729) (1 / 729) ≤ 1 / 20000 := by
    have hsqrtLo : (141 / 100 : ℝ) ≤ Real.sqrt 2 := by
      apply Real.le_sqrt_of_sq_le
      norm_num
    have hsqrtHi : Real.sqrt 2 ≤ (10 / 7 : ℝ) :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    constructor
    · unfold lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
      positivity
    · unfold lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
      have hterm1 : (78 / 5 : ℝ) / 4 * (1 / 729 : ℝ) ^ 2 ≤ 3 / 400000 := by
        norm_num
      have hratio : (78 / 5 : ℝ) / Real.sqrt 2 ≤
          (78 / 5 : ℝ) * (100 / 141 : ℝ) := by
        rw [div_le_iff₀ (Real.sqrt_pos.2 (by norm_num))]
        nlinarith only [hsqrtLo]
      have hterm2 : (36 / 25 : ℝ) * ((78 / 5 : ℝ) / Real.sqrt 2) *
          (1 / 729 : ℝ) ^ 2 ≤ 30 / 1000000 := by
        have hh := mul_le_mul_of_nonneg_right hratio
          (sq_nonneg (1 / 729 : ℝ))
        have hh' := mul_le_mul_of_nonneg_left hh
          (by norm_num : (0 : ℝ) ≤ 36 / 25)
        have hbound : (36 / 25 : ℝ) * ((78 / 5 : ℝ) * (100 / 141 : ℝ)) *
            (1 / 729 : ℝ) ^ 2 ≤ 30 / 1000000 := by norm_num
        nlinarith only [hh', hbound]
      have hterm3 : (57 / 200 : ℝ) * (78 / 5 : ℝ) *
          Real.sqrt 2 * (1 / 729 : ℝ) ^ 2 ≤ 12 / 1000000 := by
        have hh := mul_le_mul_of_nonneg_left hsqrtHi
          (by norm_num : (0 : ℝ) ≤ (57 / 200 : ℝ) * (78 / 5 : ℝ) *
            (1 / 729 : ℝ) ^ 2)
        have hbound : (57 / 200 : ℝ) * (78 / 5 : ℝ) *
            (10 / 7 : ℝ) * (1 / 729 : ℝ) ^ 2 ≤ 12 / 1000000 := by norm_num
        calc
          _ = ((57 / 200 : ℝ) * (78 / 5 : ℝ) * (1 / 729 : ℝ) ^ 2) *
              Real.sqrt 2 := by ring
          _ ≤ ((57 / 200 : ℝ) * (78 / 5 : ℝ) * (1 / 729 : ℝ) ^ 2) *
              (10 / 7 : ℝ) := hh
          _ ≤ 12 / 1000000 := by nlinarith only [hbound]
      calc
        _ = (78 / 5 : ℝ) / 4 * (1 / 729 : ℝ) ^ 2 +
              (36 / 25 : ℝ) * ((78 / 5 : ℝ) / Real.sqrt 2) *
                (1 / 729 : ℝ) ^ 2 +
              (57 / 200 : ℝ) * (78 / 5 : ℝ) * Real.sqrt 2 *
                (1 / 729 : ℝ) ^ 2 := by
          ring
        _ ≤ 1 / 20000 := by linarith only [hterm1, hterm2, hterm3]
  have hμ : pureFluxCovarianceMu
      (pureFluxCovarianceA 0 5) (pureFluxCovarianceB 0 5) ≤ 1 / 2500 := by
    simpa using old_signed_source_covariance_mu_decay 0
  have hμ0 : 0 ≤ pureFluxCovarianceMu
      (pureFluxCovarianceA 0 5) (pureFluxCovarianceB 0 5) :=
    (pureFlux_covariance_mu_lower _ _).1
  have hd : 0 ≤ 2 * lemmaVH2kn (1 / 729) (1 / 729) *
        (3683 / 2500 : ℝ) +
        pureFluxCovarianceMu (pureFluxCovarianceA 0 5)
          (pureFluxCovarianceB 0 5) * (3683 / 2500 : ℝ) ^ 2 ∧
      2 * lemmaVH2kn (1 / 729) (1 / 729) *
        (3683 / 2500 : ℝ) +
        pureFluxCovarianceMu (pureFluxCovarianceA 0 5)
          (pureFluxCovarianceB 0 5) * (3683 / 2500 : ℝ) ^ 2 ≤ 1016 / 1000000 := by
    constructor
    · have hbaseCoeff : 0 ≤ 2 * lemmaVH2kn (1 / 729) (1 / 729) *
          (3683 / 2500 : ℝ) :=
        mul_nonneg (mul_nonneg (by norm_num) hκ.1) (by norm_num)
      have hfeedbackCoeff : 0 ≤ pureFluxCovarianceMu
          (pureFluxCovarianceA 0 5) (pureFluxCovarianceB 0 5) *
          (3683 / 2500 : ℝ) ^ 2 :=
        mul_nonneg hμ0 (sq_nonneg (3683 / 2500 : ℝ))
      exact add_nonneg hbaseCoeff hfeedbackCoeff
    · nlinarith only [hκ.2, hμ]
  have hq : (1016 / 1000000 : ℝ) * (21 / 20 : ℝ) =
      10668 / 10000000 := by norm_num
  have hbracket :
      2 * (3683 / 2500 : ℝ) * C +
        4 * Aold * x *
          (2 * lemmaVH2kn (1 / 729) (1 / 729) *
              (3683 / 2500 : ℝ) * C +
            pureFluxCovarianceMu (pureFluxCovarianceA 0 5)
              (pureFluxCovarianceB 0 5) * (3683 / 2500 : ℝ) ^ 2 * C ^ 2) ≤
      2 * (3683 / 2500 : ℝ) * (1 + 12 * gamma) +
        4 * (10668 / 10000000 : ℝ) * mainRawA gamma * x := by
    have hcov :
        2 * lemmaVH2kn (1 / 729) (1 / 729) *
            (3683 / 2500 : ℝ) * C +
          pureFluxCovarianceMu (pureFluxCovarianceA 0 5)
            (pureFluxCovarianceB 0 5) * (3683 / 2500 : ℝ) ^ 2 * C ^ 2 ≤
        (2 * lemmaVH2kn (1 / 729) (1 / 729) *
            (3683 / 2500 : ℝ) +
          pureFluxCovarianceMu (pureFluxCovarianceA 0 5)
            (pureFluxCovarianceB 0 5) * (3683 / 2500 : ℝ) ^ 2) * C ^ 2 := by
      have hCsmall : C ≤ C ^ 2 := by nlinarith [hCone]
      nlinarith only [hCsmall, hκ.1, hμ0]
    have hcov2 :
        (2 * lemmaVH2kn (1 / 729) (1 / 729) *
            (3683 / 2500 : ℝ) +
          pureFluxCovarianceMu (pureFluxCovarianceA 0 5)
            (pureFluxCovarianceB 0 5) * (3683 / 2500 : ℝ) ^ 2) * C ^ 2 ≤
        (10668 / 10000000 : ℝ) := by
      calc
        _ ≤ (1016 / 1000000 : ℝ) * C ^ 2 :=
          mul_le_mul_of_nonneg_right hd.2 (sq_nonneg C)
        _ ≤ (1016 / 1000000 : ℝ) * x ^ 2 :=
          mul_le_mul_of_nonneg_left hCsq (by norm_num)
        _ ≤ (1016 / 1000000 : ℝ) * (21 / 20 : ℝ) :=
          mul_le_mul_of_nonneg_left hx2 (by norm_num)
        _ = 10668 / 10000000 := hq
    have hcov3 : 4 * Aold * x *
        (2 * lemmaVH2kn (1 / 729) (1 / 729) *
            (3683 / 2500 : ℝ) * C +
          pureFluxCovarianceMu (pureFluxCovarianceA 0 5)
            (pureFluxCovarianceB 0 5) * (3683 / 2500 : ℝ) ^ 2 * C ^ 2) ≤
        4 * (10668 / 10000000 : ℝ) * mainRawA gamma * x := by
      have hAold0 : 0 ≤ Aold := by dsimp [Aold]; positivity
      have hweight : 0 ≤ 4 * Aold * x :=
        mul_nonneg (mul_nonneg (by norm_num) hAold0) hxpos.le
      have hcovmul1 := mul_le_mul_of_nonneg_left hcov hweight
      have hcovmul2 := mul_le_mul_of_nonneg_left hcov2 hweight
      have hAcoeff : 4 * Aold * x ≤ 4 * mainRawA gamma * x := by
        calc
          _ = Aold * 4 * x := by ring
          _ ≤ mainRawA gamma * 4 * x :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hAold (by norm_num)) hxpos.le
          _ = 4 * mainRawA gamma * x := by ring
      have hAterm := mul_le_mul_of_nonneg_right hAcoeff
        (by norm_num : (0 : ℝ) ≤ 10668 / 10000000)
      calc
        _ ≤ 4 * Aold * x *
            ((2 * lemmaVH2kn (1 / 729) (1 / 729) *
                (3683 / 2500 : ℝ) +
              pureFluxCovarianceMu (pureFluxCovarianceA 0 5)
                (pureFluxCovarianceB 0 5) *
                (3683 / 2500 : ℝ) ^ 2) * C ^ 2) := hcovmul1
        _ ≤ 4 * Aold * x * (10668 / 10000000 : ℝ) := hcovmul2
        _ ≤ 4 * mainRawA gamma * x * (10668 / 10000000 : ℝ) := hAterm
        _ = 4 * (10668 / 10000000 : ℝ) * mainRawA gamma * x := by ring
    have hbase : 2 * (3683 / 2500 : ℝ) * C ≤
        2 * (3683 / 2500 : ℝ) * (1 + 12 * gamma) := by
      exact mul_le_mul_of_nonneg_left hCup (by norm_num)
    exact add_le_add hbase hcov3
  rw [hF]
  dsimp [C, x] at hbracket ⊢
  have hmul := mul_le_mul_of_nonneg_left hbracket hv
  nlinarith only [hmul]

private theorem main_old_signed_cap_le_mainMu
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (hγ : M.gamma ≤ gammaZero) :
    oldSignedMeanSourceCap M h m 5 ≤
      mainMu ((q3ModelAmplitude M h (m + 1)) ^ 2 /
        (Annealed.sigmaBar M m : ℝ) ^ 2) M.gamma := by
  let q : ℤ := m - 5
  let σ : ℝ := Annealed.sigmaBar M m
  let v : ℝ := (q3ModelAmplitude M h (m + 1)) ^ 2 / σ ^ 2
  let C : ℝ := rawTraceOldFrameP20LocalClock M.gamma 6
  let κ : ℝ := lemmaVH2kn
    (cubeScaleFactor (originCube 2 q) /
      (q3ModelLength (q + (6 : ℤ))).1)
    (diagMeshRadius (originCube 2 q) (pureFluxBankSourceDepth 6) /
      (q3ModelLength (q + (6 : ℤ))).1)
  let μ : ℝ := pureFluxCovarianceMu
    (pureFluxCovarianceA 0 5) (pureFluxCovarianceB 0 5)
  let F : ℝ := oldSignedP20Full64Cap M.gamma 6
  have hq : m - (5 : ℤ) + (6 : ℤ) = m + 1 := by omega
  have hp := old_signed_full64_depth_parameters q 0
  have hscale : cubeScaleFactor (originCube 2 q) /
      (q3ModelLength (q + (6 : ℤ))).1 = (1 / 729 : ℝ) := by
    simpa using hp.1
  have hmesh : diagMeshRadius (originCube 2 q) (pureFluxBankSourceDepth 6) /
      (q3ModelLength (q + (6 : ℤ))).1 = (1 / 729 : ℝ) := by
    simpa [pureFluxBankSourceDepth] using hp.2.1
  have hρ : pureFluxCovarianceRho 0 (6 - 1) = (1 / 729 : ℝ) := by
    simpa using hp.2.2.1
  have hδ : pureFluxCovarianceDelta 0 (6 - 1) = (1 / 729 : ℝ) := by
    simpa using hp.2.2.2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hγ0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hκ : κ = lemmaVH2kn (1 / 729) (1 / 729) := by
    change lemmaVH2kn
      (cubeScaleFactor (originCube 2 q) /
        (q3ModelLength (q + (6 : ℤ))).1)
      (diagMeshRadius (originCube 2 q) (pureFluxBankSourceDepth 6) /
        (q3ModelLength (q + (6 : ℤ))).1) = _
    rw [hscale, hmesh]
  have hcap : oldSignedMeanSourceCap M h m 5 =
      v * C * (2 * (3683 / 2500 : ℝ) +
        2 * κ * (3683 / 2500 : ℝ) * F +
        C * μ * (3683 / 2500 : ℝ) ^ 2 * F) := by
    unfold oldSignedMeanSourceCap
    simp only [show (5 : ℕ) + 1 = 6 by norm_num]
    have hqCast : m - (↑(5 : ℕ) : ℤ) + (↑(6 : ℕ) : ℤ) = m + 1 := by
      omega
    have hscaleM1 : cubeScaleFactor
        (originCube 2 (m - (↑(5 : ℕ) : ℤ))) /
        (q3ModelLength (m + 1)).1 = (1 / 729 : ℝ) := by
      rw [← hqCast]
      simpa [q] using hscale
    have hmeshM1 : diagMeshRadius
        (originCube 2 (m - (↑(5 : ℕ) : ℤ)))
        (pureFluxBankSourceDepth 6) /
        (q3ModelLength (m + 1)).1 = (1 / 729 : ℝ) := by
      rw [← hqCast]
      simpa [q] using hmesh
    rw [hqCast, hscaleM1, hmeshM1, hκ]
  have hμ : μ = pureFluxCovarianceMu
      (pureFluxCovarianceA 0 5) (pureFluxCovarianceB 0 5) := rfl
  have hF : F = oldSignedP20Full64Cap M.gamma 6 := rfl
  have hC : C = (3 : ℝ) ^ (10 * M.gamma) := by
    dsimp [C, rawTraceOldFrameP20LocalClock]
    congr 1
    ring
  have hprofile := old_signed_mean_cap_scalar_le hv hγ0 hγ
  rw [hcap, hκ, hμ, hF, hC]
  have hmain := main_mu_g9_lower hv hγ0
  have hmargin : (1 / 320000 : ℝ) ≤
      (107 / 100000 : ℝ) - (10668 / 10000000 : ℝ) := by norm_num
  have hAline : 2 + (11710534 : ℝ) * M.gamma ≤ mainRawA M.gamma := by
    dsimp [mainRawA]
    nlinarith [hγ0]
  have hxone : 1 ≤ (3 : ℝ) ^ (26 * M.gamma) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (by norm_num) hγ0)
  have hAproduct : 2 + (11710534 : ℝ) * M.gamma ≤
      mainRawA M.gamma *
        (3 : ℝ) ^ (26 * M.gamma) := by
    have hApos : 0 ≤ mainRawA M.gamma := by linarith [hAline]
    have hmul := mul_le_mul_of_nonneg_left hxone hApos
    calc
      2 + (11710534 : ℝ) * M.gamma ≤ mainRawA M.gamma := hAline
      _ ≤ mainRawA M.gamma * (3 : ℝ) ^ (26 * M.gamma) := by
        nlinarith only [hmul]
  have hApos : 0 ≤ mainRawA M.gamma := by linarith [hAline]
  have hxpos : 0 < (3 : ℝ) ^ (26 * M.gamma) := by positivity
  have hAxnonneg : 0 ≤ 4 * mainRawA M.gamma *
      (3 : ℝ) ^ (26 * M.gamma) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hApos) hxpos.le
  have hgammaSlope : 0 ≤
      (4 * (1 / 320000 : ℝ) * 11710534 -
        2 * (3683 / 2500 : ℝ) * 12) * M.gamma := by
    have hc : 0 ≤ 4 * (1 / 320000 : ℝ) * 11710534 -
        2 * (3683 / 2500 : ℝ) * 12 := by norm_num
    exact mul_nonneg hc hγ0
  have hsurplus :
      2 * (3683 / 2500 : ℝ) * (1 + 12 * M.gamma) +
          4 * (10668 / 10000000 : ℝ) * mainRawA M.gamma *
            (3 : ℝ) ^ (26 * M.gamma) ≤
        2 * mainBetaOld + (107 / 100000 : ℝ) * 4 *
          mainRawA M.gamma *
            (3 : ℝ) ^ (26 * M.gamma) := by
    have hdiff := mul_le_mul_of_nonneg_left hmargin hAxnonneg
    have hAproductPay := mul_le_mul_of_nonneg_left hAproduct
      (by norm_num : (0 : ℝ) ≤ 4 * (1 / 320000 : ℝ))
    have hbeta : mainBetaOld = (3683 / 2500 : ℝ) := by
      norm_num [mainBetaOld]
    nlinarith only [hdiff, hAproductPay, hgammaSlope, hbeta]
  exact (hprofile.trans (mul_le_mul_of_nonneg_left hsurplus hv)).trans hmain

/-- MA-ENVELOPE-A: the actual OLD-frame partial-insertion mean is bounded by
the source's literal affine envelope, with its exact `mainMu` slope. -/
theorem main_envelope_a_actual_law
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k)
    (m : ℤ) (hm : m < N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    mainMeanActual M m t ≤
      mainEnvelopeA
        ((q3ModelAmplitude M h (m + 1)) ^ 2 /
          (Annealed.sigmaBar M m : ℝ) ^ 2)
        M.gamma mainSourceMeanPrefix t := by
  have hrows := native_source_rows M h hM hγ N hpast m hm
  have hstart := main_mean_actual_initial_cap M m hrows hγ
  have hpastM : ∀ k < m, nativeInductionState M h k := by
    intro k hk
    exact hpast k (lt_trans hk hm)
  have htransport := old_signed_actual_mean_source_transport
    M h hM hγ m hpastM 5 t ht
  have hv : 0 ≤ (q3ModelAmplitude M h (m + 1)) ^ 2 /
      (Annealed.sigmaBar M m : ℝ) ^ 2 := by positivity
  have hslope := main_old_signed_cap_le_mainMu M h m hγ
  have hmul := mul_le_mul_of_nonneg_left hslope ht.1
  unfold mainEnvelopeA
  calc
    mainMeanActual M m t ≤
        mainMeanActual M m 0 +
          t * oldSignedMeanSourceCap M h m 5 := by
      simpa [mainMeanActual] using htransport
    _ ≤ mainSourceMeanPrefix + t *
        mainMu ((q3ModelAmplitude M h (m + 1)) ^ 2 /
          (Annealed.sigmaBar M m : ℝ) ^ 2) M.gamma :=
      add_le_add hstart hmul

end ASDExplicitGamma.Main
