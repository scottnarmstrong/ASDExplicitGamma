module

public import ASDExplicitGamma.Numerics.Inverse.Scalars
public import ASDExplicitGamma.Numerics.Inverse.RealBounds
public import ASDExplicitGamma.Statements.GammaZero

/-! Depth envelope arithmetic for the raw-trace band, with the exact source
constants and the corrected `h_* = 134` profile. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open ASDExplicitGamma.Numerics.Inverse

noncomputable section

def rawTraceBandFullCap (γ h : ℝ) : ℝ :=
  4 * (1009309 / 500000 + γ * (32474 * (h + 1) + 11483216)) *
    (3 : ℝ) ^ ((2 * h + 4) * γ)

def rawTraceBandClock (γ h : ℝ) : ℝ :=
  (9 / 2) * γ * (3 : ℝ) ^ (2 * γ * h)

def rawTraceBandIncrement (γ h : ℝ) : ℝ :=
  rawTraceBandClock γ h *
    ((78 * h + 76 * (521 / 1000)) * (3683 / 2500) +
      (2 * (521 / 1000) * (3683 / 2500) +
        (1975 / 1000 + 38 * (1565 / 1000)) * (3683 / 2500) ^ 2) *
        rawTraceBandFullCap γ h)

def rawTraceBandLambda (γ h : ℝ) : ℝ :=
  (3 : ℝ) ^ (2 * γ * h) *
    ((1 + 1 / 1000) * ((21 / 100) * (γ / gammaZero) +
      rawTraceBandIncrement γ h) +
      8 * (1 + 1 / (1 / 1000)) * ((11 / 10) * γ * h) ^ 2)

private theorem raw_trace_band_full_cap_split (γ d : ℝ) :
    (3 : ℝ) ^ ((2 * (134 + d) + 4) * γ) =
      (3 : ℝ) ^ ((2 * 134 + 4) * γ) * (3 : ℝ) ^ (2 * d * γ) := by
  rw [show (2 * (134 + d) + 4) * γ = (2 * 134 + 4) * γ + 2 * d * γ by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 3)]

private theorem raw_trace_band_clock_split (γ d : ℝ) :
    (3 : ℝ) ^ (2 * γ * (134 + d)) =
      (3 : ℝ) ^ (2 * γ * 134) * (3 : ℝ) ^ (2 * γ * d) := by
  rw [show 2 * γ * (134 + d) = 2 * γ * 134 + 2 * γ * d by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 3)]

/-- The full-response profile at depth `134+d` has degree one in `d` and
the explicit exponential depth factor. -/
private theorem raw_trace_band_full_cap_depth (γ : ℝ) (d : ℕ)
    (hγ0 : 0 < γ) (hγ : γ ≤ gammaZero) :
    rawTraceBandFullCap γ (134 + (d : ℝ)) ≤
      (invTraceF : ℚ) * (1 + (d : ℝ)) * (3 : ℝ) ^ (2 * gammaZero * d) := by
  have hd : 0 ≤ (d : ℝ) := by positivity
  have hγ00 : 0 < gammaZero := by norm_num [gammaZero]
  have hbaseCoeff :
      1009309 / 500000 + γ * (32474 * (134 + (d : ℝ) + 1) + 11483216) ≤
        (1009309 / 500000 + gammaZero * (32474 * (134 + 1) + 11483216)) *
          (1 + (d : ℝ)) := by
    have hγbase := mul_le_mul_of_nonneg_left hγ
      (show 0 ≤ 32474 * (134 + 1) + 11483216 by positivity)
    have hγdepth := mul_le_mul_of_nonneg_right hγ hd
    have hdom : gammaZero * 32474 ≤
        1009309 / 500000 + gammaZero * (32474 * (134 + 1) + 11483216) := by
      norm_num [gammaZero]
    have hγ00d : 0 ≤ gammaZero * (d : ℝ) := mul_nonneg hγ00.le hd
    nlinarith [hγbase, hγdepth, hγ00d, hdom]
  have hbaseExp : (3 : ℝ) ^ ((2 * 134 + 4) * γ) ≤
      (3 : ℝ) ^ ((2 * 134 + 4) * gammaZero) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    nlinarith
  have hdepthExp : (3 : ℝ) ^ (2 * (d : ℝ) * γ) ≤
      (3 : ℝ) ^ (2 * gammaZero * d) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    nlinarith
  have hcap := inv_three_power_bound ((2 * 134 + 4) * gammaZero)
    (by positivity) (by norm_num [gammaZero])
  have hcapEq :
      1 / (1 - (11 / 10 : ℝ) * ((2 * 134 + 4) * gammaZero)) =
        (invE ((11 / 10) * (2 * 134 + 4) * invGamma) : ℚ) := by
    norm_num [invE, invGamma, gammaZero]
  have hconst :
      ((invTraceF : ℚ) : ℝ) = 4 *
        (1009309 / 500000 + gammaZero * (32474 * (134 + 1) + 11483216)) *
          (invE ((11 / 10) * (2 * 134 + 4) * invGamma) : ℚ) := by
    norm_num [invTraceF, invE, invGamma, gammaZero]
  unfold rawTraceBandFullCap
  rw [raw_trace_band_full_cap_split γ (d : ℝ)]
  have hbracket0 : 0 ≤ 1009309 / 500000 +
      γ * (32474 * (134 + (d : ℝ) + 1) + 11483216) := by positivity
  have hbase0 : 0 ≤ 1009309 / 500000 +
      gammaZero * (32474 * (134 + 1) + 11483216) := by positivity
  have hpow0 : 0 ≤ (3 : ℝ) ^ ((2 * 134 + 4) * γ) := by positivity
  have hpowD : 0 ≤ (3 : ℝ) ^ (2 * (d : ℝ) * γ) := by positivity
  calc
    _ ≤ 4 * ((1009309 / 500000 + gammaZero *
          (32474 * (134 + 1) + 11483216)) * (1 + (d : ℝ))) *
        ((3 : ℝ) ^ ((2 * 134 + 4) * gammaZero) *
          (3 : ℝ) ^ (2 * gammaZero * d)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hbaseCoeff (by norm_num))
        (mul_le_mul hbaseExp hdepthExp hpowD (by positivity))
        (by positivity) (by positivity)
    _ ≤ 4 * ((1009309 / 500000 + gammaZero *
          (32474 * (134 + 1) + 11483216)) * (1 + (d : ℝ))) *
        ((invE ((11 / 10) * (2 * 134 + 4) * invGamma) : ℚ) *
          (3 : ℝ) ^ (2 * gammaZero * d)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right (hcap.trans_eq hcapEq) (by positivity)
      · positivity
    _ = (invTraceF : ℚ) * (1 + (d : ℝ)) *
        (3 : ℝ) ^ (2 * gammaZero * d) := by
      calc
        _ = (4 * (1009309 / 500000 + gammaZero *
              (32474 * (134 + 1) + 11483216)) *
              (invE ((11 / 10) * (2 * 134 + 4) * invGamma) : ℚ)) *
            (1 + (d : ℝ)) * (3 : ℝ) ^ (2 * gammaZero * d) := by ring
        _ = _ := by rw [← hconst]

/-- The accumulated shell clock has exactly one factor of `theta` and two
depth powers after fixing the first 134 shells. -/
private theorem raw_trace_band_clock_depth (γ : ℝ) (d : ℕ)
    (hγ0 : 0 < γ) (hγ : γ ≤ gammaZero) :
    rawTraceBandClock γ (134 + (d : ℝ)) ≤
      (γ / gammaZero) * (invTraceClock : ℚ) *
        (3 : ℝ) ^ (2 * gammaZero * d) := by
  have hd : 0 ≤ (d : ℝ) := by positivity
  have hγ00 : 0 < gammaZero := by norm_num [gammaZero]
  have hbaseExp : (3 : ℝ) ^ (2 * γ * 134) ≤
      (3 : ℝ) ^ (2 * gammaZero * 134) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    nlinarith
  have hdepthExp : (3 : ℝ) ^ (2 * γ * (d : ℝ)) ≤
      (3 : ℝ) ^ (2 * gammaZero * d) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    nlinarith
  have hcap := inv_three_power_bound (2 * 134 * gammaZero)
    (by positivity) (by norm_num [gammaZero])
  have hcapEq :
      1 / (1 - (11 / 10 : ℝ) * (2 * 134 * gammaZero)) =
        (invE ((11 / 10) * 2 * 134 * invGamma) : ℚ) := by
    norm_num [invE, invGamma, gammaZero]
  have hconst :
      ((invTraceClock : ℚ) : ℝ) =
        (9 / 2) * gammaZero *
          (invE ((11 / 10) * 2 * 134 * invGamma) : ℚ) := by
    norm_num [invTraceClock, invE, invGamma, gammaZero]
  unfold rawTraceBandClock
  rw [raw_trace_band_clock_split γ (d : ℝ)]
  have hgamma : γ = (γ / gammaZero) * gammaZero := by
    field_simp [ne_of_gt hγ00]
  have hbase0 : 0 ≤ (3 : ℝ) ^ (2 * γ * 134) := by positivity
  have hdepth0 : 0 ≤ (3 : ℝ) ^ (2 * γ * (d : ℝ)) := by positivity
  calc
    _ ≤ (9 / 2) * γ *
        ((3 : ℝ) ^ (2 * gammaZero * 134) *
          (3 : ℝ) ^ (2 * gammaZero * d)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hbaseExp hdepthExp hdepth0 (by positivity)) (by positivity)
    _ ≤ (γ / gammaZero) * (9 / 2) * gammaZero *
        ((invE ((11 / 10) * 2 * 134 * invGamma) : ℚ) *
          (3 : ℝ) ^ (2 * gammaZero * d)) := by
      have hcap' : (3 : ℝ) ^ (2 * gammaZero * 134) ≤
          1 / (1 - (11 / 10 : ℝ) * (2 * gammaZero * 134)) := by
        convert hcap using 1 <;> ring_nf
      have hcapEq' :
          1 / (1 - (11 / 10 : ℝ) * (2 * gammaZero * 134)) =
            (invE ((11 / 10) * 2 * 134 * invGamma) : ℚ) := by
        convert hcapEq using 1; ring_nf
      have hbaseCap : (3 : ℝ) ^ (2 * gammaZero * 134) ≤
          (invE ((11 / 10) * 2 * 134 * invGamma) : ℚ) := hcap'.trans_eq hcapEq'
      have htheta : (γ / gammaZero) * (9 / 2) * gammaZero = (9 / 2) * γ := by
        field_simp [ne_of_gt hγ00]
      rw [htheta]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hbaseCap le_rfl (by positivity)
          (by norm_num [invE, invGamma])) (by positivity)
    _ = (γ / gammaZero) *
        ((9 / 2) * gammaZero *
          (invE ((11 / 10) * 2 * 134 * invGamma) : ℚ)) *
        (3 : ℝ) ^ (2 * gammaZero * d) := by ring
    _ = _ := by rw [← hconst]

/-- The corrected h-dependent scalar envelope. Its constant at depth zero is
the certified source rational `invTraceM`; the factors at additional depth
have degree at most two and exponential rate `6 gammaZero`. -/
private theorem raw_trace_band_increment_depth (γ : ℝ) (d : ℕ)
    (hγ0 : 0 < γ) (hγ : γ ≤ gammaZero) :
    rawTraceBandIncrement γ (134 + (d : ℝ)) ≤
      (γ / gammaZero) * (invTraceC : ℚ) * (1 + (d : ℝ)) *
        (3 : ℝ) ^ (4 * gammaZero * d) := by
  have hd : 0 ≤ (d : ℝ) := by positivity
  have hγ00 : 0 < gammaZero := by norm_num [gammaZero]
  have hfull := raw_trace_band_full_cap_depth γ d hγ0 hγ
  have hclock := raw_trace_band_clock_depth γ d hγ0 hγ
  have hpowd : 1 ≤ (3 : ℝ) ^ (2 * gammaZero * d) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hrows :
      (78 * (134 + (d : ℝ)) + 76 * (521 / 1000)) * (3683 / 2500) +
          (2 * (521 / 1000) * (3683 / 2500) +
            (1975 / 1000 + 38 * (1565 / 1000)) * (3683 / 2500) ^ 2) *
            rawTraceBandFullCap γ (134 + (d : ℝ)) ≤
        ((78 * 134 + 76 * (521 / 1000)) * (3683 / 2500) +
          (2 * (521 / 1000) * (3683 / 2500) +
            (1975 / 1000 + 38 * (1565 / 1000)) * (3683 / 2500) ^ 2) *
            (invTraceF : ℚ)) *
          (1 + (d : ℝ)) * (3 : ℝ) ^ (2 * gammaZero * d) := by
    have hlinear :
        (78 * (134 + (d : ℝ)) + 76 * (521 / 1000)) * (3683 / 2500) ≤
          ((78 * 134 + 76 * (521 / 1000)) * (3683 / 2500)) *
            (1 + (d : ℝ)) := by
      nlinarith [mul_nonneg hd (show 78 * (3683 / 2500 : ℝ) ≥ 0 by positivity)]
    have hmix0 : (0 : ℝ) ≤
        2 * (521 / 1000) * (3683 / 2500) +
          (1975 / 1000 + 38 * (1565 / 1000)) * (3683 / 2500) ^ 2 := by positivity
    have hmix := mul_le_mul_of_nonneg_left hfull hmix0
    have hlinearQ :
        (78 * (134 + (d : ℝ)) + 76 * (521 / 1000)) * (3683 / 2500) ≤
          ((78 * 134 + 76 * (521 / 1000)) * (3683 / 2500)) *
            (1 + (d : ℝ)) * (3 : ℝ) ^ (2 * gammaZero * d) := by
      calc
        _ ≤ ((78 * 134 + 76 * (521 / 1000)) * (3683 / 2500)) *
            (1 + (d : ℝ)) := hlinear
        _ = (((78 * 134 + 76 * (521 / 1000)) * (3683 / 2500)) *
              (1 + (d : ℝ))) * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hpowd (by positivity)
    calc
      _ = (78 * (134 + (d : ℝ)) + 76 * (521 / 1000)) * (3683 / 2500) +
          (2 * (521 / 1000) * (3683 / 2500) +
            (1975 / 1000 + 38 * (1565 / 1000)) * (3683 / 2500) ^ 2) *
            rawTraceBandFullCap γ (134 + (d : ℝ)) := by ring
      _ ≤ ((78 * 134 + 76 * (521 / 1000)) * (3683 / 2500)) *
            (1 + (d : ℝ)) * (3 : ℝ) ^ (2 * gammaZero * d) +
          (2 * (521 / 1000) * (3683 / 2500) +
            (1975 / 1000 + 38 * (1565 / 1000)) * (3683 / 2500) ^ 2) *
            ((invTraceF : ℚ) * (1 + (d : ℝ)) *
              (3 : ℝ) ^ (2 * gammaZero * d)) := add_le_add hlinearQ hmix
      _ = _ := by ring
  have hq4 : (3 : ℝ) ^ (4 * gammaZero * (d : ℝ)) =
      ((3 : ℝ) ^ (2 * gammaZero * d)) ^ 2 := by
    rw [show 4 * gammaZero * (d : ℝ) =
      2 * gammaZero * d + 2 * gammaZero * d by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    ring
  have hbaseRows :
      ((78 * 134 + 76 * (521 / 1000)) * (3683 / 2500) +
          (2 * (521 / 1000) * (3683 / 2500) +
            (1975 / 1000 + 38 * (1565 / 1000)) * (3683 / 2500) ^ 2) *
            (invTraceF : ℚ)) * (invTraceClock : ℚ) = (invTraceC : ℚ) := by
    unfold invTraceC
    ring
  have hbaseRowsReal :
      (((78 * 134 + 76 * (521 / 1000)) * (3683 / 2500) +
        (2 * (521 / 1000) * (3683 / 2500) +
          (1975 / 1000 + 38 * (1565 / 1000)) * (3683 / 2500) ^ 2) *
            (invTraceF : ℚ)) * (invTraceClock : ℚ) : ℝ) = invTraceC := by
    norm_num [invTraceC, invTraceF, invTraceClock, invE, invGamma, gammaZero]
  have hF : 0 ≤ (invTraceF : ℝ) := by
    norm_num [invTraceF, invE, invGamma, gammaZero]
  have hrowsBound0 : 0 ≤
      (((78 * 134 + 76 * (521 / 1000)) * (3683 / 2500) +
        (2 * (521 / 1000) * (3683 / 2500) +
          (1975 / 1000 + 38 * (1565 / 1000)) * (3683 / 2500) ^ 2) *
          (invTraceF : ℚ)) * (1 + (d : ℝ)) *
        (3 : ℝ) ^ (2 * gammaZero * d) : ℝ) := by
    apply mul_nonneg
    · apply mul_nonneg
      · apply add_nonneg
        · positivity
        · exact mul_nonneg (by positivity) hF
      · linarith [hd]
    · positivity
  calc
    _ ≤ rawTraceBandClock γ (134 + (d : ℝ)) *
          (((78 * 134 + 76 * (521 / 1000)) * (3683 / 2500) +
            (2 * (521 / 1000) * (3683 / 2500) +
              (1975 / 1000 + 38 * (1565 / 1000)) * (3683 / 2500) ^ 2) *
              (invTraceF : ℚ)) * (1 + (d : ℝ)) *
            (3 : ℝ) ^ (2 * gammaZero * d)) :=
      mul_le_mul_of_nonneg_left hrows (by unfold rawTraceBandClock; positivity)
    _ ≤ ((γ / gammaZero) * (invTraceClock : ℚ) *
          (3 : ℝ) ^ (2 * gammaZero * d)) *
          (((78 * 134 + 76 * (521 / 1000)) * (3683 / 2500) +
            (2 * (521 / 1000) * (3683 / 2500) +
              (1975 / 1000 + 38 * (1565 / 1000)) * (3683 / 2500) ^ 2) *
              (invTraceF : ℚ)) * (1 + (d : ℝ)) *
            (3 : ℝ) ^ (2 * gammaZero * d)) :=
      mul_le_mul_of_nonneg_right hclock hrowsBound0
    _ = (γ / gammaZero) * (invTraceC : ℚ) *
        (1 + (d : ℝ)) * (3 : ℝ) ^ (4 * gammaZero * d) := by
      rw [hq4, ← hbaseRowsReal]
      ring

private theorem raw_trace_band_lambda_core_depth (γ : ℝ) (d : ℕ)
    (hγ0 : 0 < γ) (hγ : γ ≤ gammaZero)
    (hinc : rawTraceBandIncrement γ (134 + (d : ℝ)) ≤
      (γ / gammaZero) * (invTraceC : ℚ) * (1 + (d : ℝ)) *
        (3 : ℝ) ^ (4 * gammaZero * d)) :
    (1 + 1 / 1000 : ℝ) * ((21 / 100) * (γ / gammaZero) +
        rawTraceBandIncrement γ (134 + (d : ℝ))) +
      8 * (1 + 1 / (1 / 1000 : ℝ)) * ((11 / 10) * γ * (134 + (d : ℝ))) ^ 2 ≤
    (γ / gammaZero) *
      ((1 + 1 / 1000) * ((21 / 100) + (invTraceC : ℚ)) +
        8 * (1 + 1 / (1 / 1000 : ℚ)) *
          ((11 / 10) * invGamma * 134) ^ 2) *
      (1 + (d : ℝ)) ^ 2 * (3 : ℝ) ^ (4 * gammaZero * d) := by
  have hd : 0 ≤ (d : ℝ) := by positivity
  have hγ00 : 0 < gammaZero := by norm_num [gammaZero]
  have htheta0 : 0 ≤ γ / gammaZero := div_nonneg hγ0.le hγ00.le
  have hframe :
      8 * (1 + 1 / (1 / 1000 : ℝ)) * ((11 / 10) * γ * (134 + (d : ℝ))) ^ 2 ≤
        (γ / gammaZero) *
          (8 * (1 + 1 / (1 / 1000 : ℝ)) * ((11 / 10) * gammaZero * 134) ^ 2) *
            (1 + (d : ℝ)) ^ 2 := by
    have hdepth : 134 + (d : ℝ) ≤ 134 * (1 + (d : ℝ)) := by nlinarith
    let θ : ℝ := γ / gammaZero
    have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
    have hγ2 : γ ^ 2 ≤ θ * gammaZero ^ 2 := by
      have hprod : γ * γ ≤ γ * gammaZero :=
        mul_le_mul_of_nonneg_left hγ (le_of_lt hγ0)
      have heq : γ * gammaZero = θ * gammaZero ^ 2 := by
        dsimp [θ]
        field_simp [ne_of_gt hγ00]
      nlinarith [hprod, heq]
    have hdepth2 : (134 + (d : ℝ)) ^ 2 ≤ 134 ^ 2 * (1 + (d : ℝ)) ^ 2 := by
      calc
        _ ≤ (134 * (1 + (d : ℝ))) ^ 2 :=
          (sq_le_sq₀ (by positivity) (by positivity)).2 hdepth
        _ = 134 ^ 2 * (1 + (d : ℝ)) ^ 2 := by ring
    calc
      _ = (8 * (1 + 1 / (1 / 1000 : ℝ)) * (11 / 10 : ℝ) ^ 2) *
            (γ ^ 2 * (134 + (d : ℝ)) ^ 2) := by ring
      _ ≤ (8 * (1 + 1 / (1 / 1000 : ℝ)) * (11 / 10 : ℝ) ^ 2) *
            ((θ * gammaZero ^ 2) * (134 ^ 2 * (1 + (d : ℝ)) ^ 2)) := by gcongr
      _ = _ := by dsimp [θ]; ring
  have hP : 1 ≤ 1 + (d : ℝ) := by nlinarith [hd]
  have hP2 : 1 + (d : ℝ) ≤ (1 + (d : ℝ)) ^ 2 := by nlinarith
  have hQ4 : 1 ≤ (3 : ℝ) ^ (4 * gammaZero * d) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hbaseStart : (21 / 100) * (γ / gammaZero) ≤
      (γ / gammaZero) * (21 / 100) * (1 + (d : ℝ)) ^ 2 := by
    nlinarith [mul_nonneg htheta0 (sq_nonneg (d : ℝ))]
  have hstartCore :
      (1 + 1 / 1000 : ℝ) * ((21 / 100) * (γ / gammaZero)) ≤
        (γ / gammaZero) * ((1 + 1 / 1000) * (21 / 100)) *
          (1 + (d : ℝ)) ^ 2 * (3 : ℝ) ^ (4 * gammaZero * d) := by
    have hstart := mul_le_mul_of_nonneg_left hbaseStart
      (by norm_num : (0 : ℝ) ≤ 1 + 1 / 1000)
    calc
      _ ≤ (γ / gammaZero) * ((1 + 1 / 1000) * (21 / 100)) *
          (1 + (d : ℝ)) ^ 2 := by nlinarith [hstart]
      _ ≤ _ := by
        calc
          _ = ((γ / gammaZero) * ((1 + 1 / 1000) * (21 / 100)) *
              (1 + (d : ℝ)) ^ 2) * 1 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hQ4
            (mul_nonneg (mul_nonneg htheta0 (by positivity))
              (sq_nonneg (1 + (d : ℝ))))
  have hC : 0 ≤ (invTraceC : ℝ) := by
    norm_num [invTraceC, invTraceF, invTraceClock, invE, invGamma, gammaZero]
  have hcoeff : 0 ≤ (γ / gammaZero) * (invTraceC : ℚ) :=
    mul_nonneg htheta0 hC
  have hinc' := mul_le_mul_of_nonneg_left hinc
    (by norm_num : (0 : ℝ) ≤ 1 + 1 / 1000)
  have hincP :
      (γ / gammaZero) * (invTraceC : ℚ) * (1 + (d : ℝ)) *
          (3 : ℝ) ^ (4 * gammaZero * d) ≤
        (γ / gammaZero) * (invTraceC : ℚ) * (1 + (d : ℝ)) ^ 2 *
          (3 : ℝ) ^ (4 * gammaZero * d) := by
    calc
      _ = ((γ / gammaZero) * (invTraceC : ℚ) * (1 + (d : ℝ))) *
          (3 : ℝ) ^ (4 * gammaZero * d) := by ring
      _ ≤ ((γ / gammaZero) * (invTraceC : ℚ) * (1 + (d : ℝ)) ^ 2) *
          (3 : ℝ) ^ (4 * gammaZero * d) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hP2 hcoeff) (by positivity)
      _ = _ := by ring
  have hincCore :
      (1 + 1 / 1000 : ℝ) * rawTraceBandIncrement γ (134 + (d : ℝ)) ≤
        (γ / gammaZero) * ((1 + 1 / 1000) * (invTraceC : ℚ)) *
          (1 + (d : ℝ)) ^ 2 * (3 : ℝ) ^ (4 * gammaZero * d) := by
    calc
      _ ≤ (1 + 1 / 1000) *
          ((γ / gammaZero) * (invTraceC : ℚ) * (1 + (d : ℝ)) *
            (3 : ℝ) ^ (4 * gammaZero * d)) := hinc'
      _ ≤ (1 + 1 / 1000) *
          ((γ / gammaZero) * (invTraceC : ℚ) * (1 + (d : ℝ)) ^ 2 *
            (3 : ℝ) ^ (4 * gammaZero * d)) :=
        mul_le_mul_of_nonneg_left hincP
          (by norm_num : (0 : ℝ) ≤ 1 + 1 / 1000)
      _ = _ := by ring
  have hframeθ :
      (γ / gammaZero) *
          (8 * (1 + 1 / (1 / 1000 : ℝ)) * ((11 / 10) * gammaZero * 134) ^ 2) =
        (γ / gammaZero) *
          (8 * (1 + 1 / (1 / 1000 : ℚ)) * ((11 / 10) * invGamma * 134) ^ 2) := by
    norm_num [invGamma, gammaZero]
  have hframe' := hframe
  rw [hframeθ] at hframe'
  have hframeCoeff0 : 0 ≤
      8 * (1 + 1 / ((1 / 1000 : ℚ) : ℝ)) *
        ((11 / 10 : ℝ) * (invGamma : ℚ) * 134) ^ 2 := by
    norm_num [invGamma]
  have hframeCore :
      8 * (1 + 1 / (1 / 1000 : ℝ)) * ((11 / 10) * γ * (134 + (d : ℝ))) ^ 2 ≤
        (γ / gammaZero) *
          (8 * (1 + 1 / (1 / 1000 : ℚ)) * ((11 / 10) * invGamma * 134) ^ 2) *
          (1 + (d : ℝ)) ^ 2 * (3 : ℝ) ^ (4 * gammaZero * d) := by
    calc
      _ ≤ (γ / gammaZero) *
          (8 * (1 + 1 / (1 / 1000 : ℚ)) * ((11 / 10) * invGamma * 134) ^ 2) *
          (1 + (d : ℝ)) ^ 2 := hframe'
      _ ≤ _ := by
        calc
          _ = ((γ / gammaZero) *
              (8 * (1 + 1 / (1 / 1000 : ℚ)) * ((11 / 10) * invGamma * 134) ^ 2) *
              (1 + (d : ℝ)) ^ 2) * 1 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hQ4
            (mul_nonneg (mul_nonneg htheta0 hframeCoeff0)
              (sq_nonneg (1 + (d : ℝ))))
  calc
    _ = (1 + 1 / 1000 : ℝ) * ((21 / 100) * (γ / gammaZero)) +
        (1 + 1 / 1000) * rawTraceBandIncrement γ (134 + (d : ℝ)) +
        8 * (1 + 1 / (1 / 1000 : ℝ)) * ((11 / 10) * γ * (134 + (d : ℝ))) ^ 2 := by
      unfold rawTraceBandIncrement
      ring_nf
    _ ≤ _ := add_le_add (add_le_add hstartCore hincCore) hframeCore
    _ = _ := by ring

theorem raw_trace_band_depth_profile (γ : ℝ) (d : ℕ)
    (hγ0 : 0 < γ) (hγ : γ ≤ gammaZero) :
    rawTraceBandLambda γ (134 + (d : ℝ)) ≤
      (γ / gammaZero) * (invTraceM : ℚ) *
        (1 + (d : ℝ)) ^ 2 * (3 : ℝ) ^ (6 * gammaZero * d) := by
  have hγ00 : 0 < gammaZero := by norm_num [gammaZero]
  have hinc := raw_trace_band_increment_depth γ d hγ0 hγ
  have hLambdaCore := raw_trace_band_lambda_core_depth γ d hγ0 hγ hinc
  have hanchor := inv_three_power_bound (2 * gammaZero * 134)
    (by positivity) (by norm_num [gammaZero])
  have hanchorEq :
      1 / (1 - (11 / 10 : ℝ) * (2 * gammaZero * 134)) =
        (invE ((11 / 10) * 2 * invGamma * 134) : ℚ) := by
    norm_num [invE, invGamma, gammaZero]
  have hbasePow :
      (3 : ℝ) ^ (2 * γ * (134 + (d : ℝ))) ≤
        (invE ((11 / 10) * 2 * invGamma * 134) : ℚ) *
          (3 : ℝ) ^ (2 * gammaZero * d) := by
    rw [raw_trace_band_clock_split γ (d : ℝ)]
    have hbaseExp : (3 : ℝ) ^ (2 * γ * 134) ≤
        (3 : ℝ) ^ (2 * gammaZero * 134) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      nlinarith
    have hdepthExp : (3 : ℝ) ^ (2 * γ * (d : ℝ)) ≤
        (3 : ℝ) ^ (2 * gammaZero * d) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      nlinarith
    have hbaseCap : (3 : ℝ) ^ (2 * γ * 134) ≤
        (invE ((11 / 10) * 2 * invGamma * 134) : ℚ) := by
      calc
        _ ≤ (3 : ℝ) ^ (2 * gammaZero * 134) := hbaseExp
        _ ≤ 1 / (1 - (11 / 10 : ℝ) * (2 * gammaZero * 134)) := hanchor
        _ = (invE ((11 / 10) * 2 * invGamma * 134) : ℚ) := hanchorEq
    exact mul_le_mul hbaseCap hdepthExp (by positivity)
      (by norm_num [invE, invGamma])
  have hcore0 : 0 ≤
      (1 + 1 / 1000 : ℝ) * ((21 / 100) * (γ / gammaZero) +
        rawTraceBandIncrement γ (134 + (d : ℝ))) +
        8 * (1 + 1 / (1 / 1000 : ℝ)) * ((11 / 10) * γ * (134 + (d : ℝ))) ^ 2 := by
    have hθ : 0 ≤ γ / gammaZero := div_nonneg hγ0.le hγ00.le
    have hinc0 : 0 ≤ rawTraceBandIncrement γ (134 + (d : ℝ)) := by
      unfold rawTraceBandIncrement rawTraceBandClock rawTraceBandFullCap
      positivity
    apply add_nonneg
    · exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg (by norm_num) hθ) hinc0)
    · positivity
  have hinvE0 : 0 ≤ (invE ((11 / 10) * 2 * invGamma * 134) : ℚ) := by
    norm_num [invE, invGamma, gammaZero]
  have hinvEReal : 0 ≤ ((invE ((11 / 10) * 2 * invGamma * 134) : ℚ) : ℝ) := by
    exact_mod_cast hinvE0
  have houter0 : 0 ≤ (invE ((11 / 10) * 2 * invGamma * 134) : ℚ) *
      (3 : ℝ) ^ (2 * gammaZero * d) :=
    mul_nonneg hinvEReal (by positivity)
  have hprofileConst :
      ((invE ((11 / 10) * 2 * invGamma * 134) : ℚ) : ℝ) *
        ((1 + 1 / 1000 : ℝ) * ((21 / 100 : ℝ) + (invTraceC : ℚ)) +
          8 * (1 + 1 / (1 / 1000 : ℝ)) *
            ((11 / 10 : ℝ) * (invGamma : ℚ) * 134) ^ 2) =
        (invTraceM : ℚ) := by
    norm_num [invTraceM, invE, invGamma, invTraceC, invTraceClock, invTraceF, gammaZero]
  calc
    rawTraceBandLambda γ (134 + (d : ℝ)) = _ := rfl
    _ ≤ ((invE ((11 / 10) * 2 * invGamma * 134) : ℚ) *
          (3 : ℝ) ^ (2 * gammaZero * d)) *
        ((γ / gammaZero) *
          ((1 + 1 / 1000) * ((21 / 100) + (invTraceC : ℚ)) +
            8 * (1 + 1 / (1 / 1000 : ℚ)) *
              ((11 / 10) * invGamma * 134) ^ 2) *
          (1 + (d : ℝ)) ^ 2 * (3 : ℝ) ^ (4 * gammaZero * d)) := by
      calc
        _ ≤ ((invE ((11 / 10) * 2 * invGamma * 134) : ℚ) *
              (3 : ℝ) ^ (2 * gammaZero * d)) *
            ((1 + 1 / 1000 : ℝ) * ((21 / 100) * (γ / gammaZero) +
                rawTraceBandIncrement γ (134 + (d : ℝ))) +
              8 * (1 + 1 / (1 / 1000 : ℝ)) *
                ((11 / 10) * γ * (134 + (d : ℝ))) ^ 2) :=
          mul_le_mul_of_nonneg_right hbasePow hcore0
        _ ≤ _ := mul_le_mul_of_nonneg_left hLambdaCore houter0
    _ = (γ / gammaZero) * (invTraceM : ℚ) *
        (1 + (d : ℝ)) ^ 2 * (3 : ℝ) ^ (6 * gammaZero * d) := by
      rw [show 6 * gammaZero * (d : ℝ) =
        2 * gammaZero * d + 4 * gammaZero * d by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      calc
        _ = (γ / gammaZero) *
              (((invE ((11 / 10) * 2 * invGamma * 134) : ℚ) : ℝ) *
                ((1 + 1 / 1000 : ℝ) * ((21 / 100 : ℝ) + (invTraceC : ℚ)) +
                  8 * (1 + 1 / (1 / 1000 : ℝ)) *
                    ((11 / 10 : ℝ) * (invGamma : ℚ) * 134) ^ 2)) *
              (1 + (d : ℝ)) ^ 2 *
              ((3 : ℝ) ^ (2 * gammaZero * d) * (3 : ℝ) ^ (4 * gammaZero * d)) := by ring
        _ = _ := by rw [hprofileConst]

end

end ASDExplicitGamma.Inverse
