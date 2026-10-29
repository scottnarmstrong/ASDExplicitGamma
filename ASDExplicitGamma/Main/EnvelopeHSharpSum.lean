module

public import ASDExplicitGamma.Main.EnvelopeHSharpControl
public import ASDExplicitGamma.Main.EnvelopeHMaxHistory

/-! The beta'-discounted fixed-old-frame p = 20 control sum is bounded by the explicit
slope `δ'_H`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Model ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  Algsuperdiff.Section3 MeasureTheory

/-- History slope `δ'_H(γ)`. -/
noncomputable def mainDeltaH35 (gamma : ℝ) : ℝ :=
  (1 - mainAlpha) *
    ((540 * gamma * (3 : ℝ) ^ (12 * gamma)) /
        (1 - mainBetaPrime * (3 : ℝ) ^ (2 * gamma)) +
      ((9 / 10 : ℝ) * gamma * (3 : ℝ) ^ (48 * gamma)) *
        (mainRawA gamma / (1 - mainBetaPrime * (3 : ℝ) ^ (8 * gamma) * (1 / 9 : ℝ)) +
          mainRawS gamma * ((mainBetaPrime * (3 : ℝ) ^ (8 * gamma) * (1 / 9 : ℝ)) /
            (1 - mainBetaPrime * (3 : ℝ) ^ (8 * gamma) * (1 / 9 : ℝ)) ^ 2)))

private theorem main_three_rpow_one_sixteenth_le_four_thirds' :
    (3 : ℝ) ^ (1 / 16 : ℝ) ≤ 4 / 3 := by
  have hroot : ((3 : ℝ) ^ (1 / 16 : ℝ)) ^ (16 : ℕ) = 3 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hpower : ((3 : ℝ) ^ (1 / 16 : ℝ)) ^ (16 : ℕ) ≤
      (4 / 3 : ℝ) ^ (16 : ℕ) := by
    rw [hroot]
    norm_num
  exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num)
    (by norm_num : (16 : ℕ) ≠ 0)).1 hpower

private theorem main_three_rpow_neg_one_seventh_le_six_sevenths' :
    (3 : ℝ) ^ (-(1 / 7 : ℝ)) ≤ 6 / 7 := by
  have hroot : ((3 : ℝ) ^ (-(1 / 7 : ℝ))) ^ (7 : ℕ) = 1 / 3 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hpower : ((3 : ℝ) ^ (-(1 / 7 : ℝ))) ^ (7 : ℕ) ≤
      (6 / 7 : ℝ) ^ (7 : ℕ) := by
    rw [hroot]
    norm_num
  exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num)
    (by norm_num : (7 : ℕ) ≠ 0)).1 hpower

theorem main_rawShell_fixed_old_frame_p20_control_beta_discounted_le_deltaH35
    (M : ABKModel 2) (h : ℝ) (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n) :
    Summable (fun j : ℕ => mainBetaPrime ^ j *
      mainRawShellOldFrameP20Control M h m j) ∧
    (1 - mainAlpha) * ∑' j : ℕ, mainBetaPrime ^ j *
      mainRawShellOldFrameP20Control M h m j ≤ mainDeltaH35 M.gamma := by
  let gamma : ℝ := M.gamma
  let alpha : ℝ := mainAlpha
  let beta : ℝ := mainBetaPrime
  let r0 : ℝ := beta * (3 : ℝ) ^ (2 * gamma)
  let r1 : ℝ := beta * (3 : ℝ) ^ (8 * gamma) * (1 / 9 : ℝ)
  let a : ℝ := mainRawA gamma
  let b : ℝ := mainRawS gamma
  let baseCoeff : ℝ := 540 * gamma * (3 : ℝ) ^ (12 * gamma)
  let nonlinearCoeff : ℝ := (9 / 10 : ℝ) * gamma * (3 : ℝ) ^ (48 * gamma)
  let majorant : ℕ → ℝ := fun j =>
    baseCoeff * r0 ^ j + nonlinearCoeff * (a + b * (j : ℝ)) * r1 ^ j
  have hgamma0 : 0 ≤ gamma := by
    dsimp [gamma]
    exact M.shellPrefix.gamma_pos.le
  have hgamma' : gamma ≤ 17 / 50000 := by
    simpa [gamma, gammaZero] using hgamma
  have hpow12 : (3 : ℝ) ^ (12 * gamma) ≤ 4 / 3 := by
    have hexp : 12 * gamma ≤ 1 / 16 := by nlinarith
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp).trans
      main_three_rpow_one_sixteenth_le_four_thirds'
  have hpow48 : (3 : ℝ) ^ (48 * gamma) ≤ 4 / 3 := by
    have hexp : 48 * gamma ≤ 1 / 16 := by nlinarith
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp).trans
      main_three_rpow_one_sixteenth_le_four_thirds'
  have ha : a ≤ 4000 := by
    dsimp [a, gamma, mainRawA]
    nlinarith [hgamma']
  have hb : b ≤ 12 := by
    dsimp [b, gamma, mainRawS]
    nlinarith [hgamma']
  have hr1o : beta * (3 : ℝ) ^ (8 * gamma) = (3 : ℝ) ^ (8 * gamma - 3 / 20) := by
    dsimp [beta, mainBetaPrime]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hr1eq : r1 = (3 : ℝ) ^ (8 * gamma - 3 / 20) * (1 / 9 : ℝ) := by
    dsimp [r1]; rw [hr1o]
  have hr0eq : r0 = (3 : ℝ) ^ (2 * gamma - 3 / 20) := by
    dsimp [r0, beta, mainBetaPrime]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hexpBeta : 8 * gamma - 3 / 20 ≤ -(1 / 7 : ℝ) := by
    norm_num at hgamma'
    norm_num
    nlinarith
  have hr1obound : (3 : ℝ) ^ (8 * gamma - 3 / 20) ≤ 6 / 7 :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpBeta).trans
      main_three_rpow_neg_one_seventh_le_six_sevenths'
  have hr1bound : r1 ≤ 6 / 7 := by
    rw [hr1eq]; nlinarith [hr1obound]
  have hbeta0 : 0 ≤ beta := by
    dsimp [beta, mainBetaPrime]
    exact Real.rpow_nonneg (by norm_num) _
  have hr0nonneg : 0 ≤ r0 := by
    dsimp [r0]
    exact mul_nonneg hbeta0 (Real.rpow_nonneg (by norm_num) _)
  have hr1nonneg : 0 ≤ r1 := by
    dsimp [r1]
    exact mul_nonneg (mul_nonneg hbeta0 (Real.rpow_nonneg (by norm_num) _)) (by norm_num)
  have hr0le : r0 ≤ (3 : ℝ) ^ (8 * gamma - 3 / 20) := by
    rw [hr0eq]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hgamma0])
  have hr0bound : r0 ≤ 6 / 7 := hr0le.trans hr1obound
  have hAlpha4 : alpha ^ 4 = (1 / 3 : ℝ) := by
    dsimp [alpha, mainAlpha]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num [Real.rpow_neg_one]
  have hAlphaLow : 3 / 4 ≤ alpha := by
    have hAlpha0 : 0 ≤ alpha := by dsimp [alpha, mainAlpha]; positivity
    apply (pow_le_pow_iff_left₀ (by norm_num) hAlpha0
      (by norm_num : (4 : ℕ) ≠ 0)).1
    rw [hAlpha4]
    norm_num
  have hAlphaOne : alpha ≤ 1 := by
    dsimp [alpha, mainAlpha]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hweight : 0 ≤ 1 - alpha ∧ 1 - alpha ≤ 1 / 4 := by
    exact ⟨by linarith [hAlphaOne], by linarith [hAlphaLow]⟩
  have hr0norm : ‖r0‖ < 1 := by
    rw [Real.norm_of_nonneg hr0nonneg]
    linarith
  have hr1norm : ‖r1‖ < 1 := by
    rw [Real.norm_of_nonneg hr1nonneg]
    linarith
  have hgeo0 := hasSum_geometric_of_norm_lt_one hr0norm
  have hgeo1 := hasSum_geometric_of_norm_lt_one hr1norm
  have hlinear1 := hasSum_coe_mul_geometric_of_norm_lt_one hr1norm
  have hpolySummable : Summable (fun j : ℕ =>
      (a + b * (j : ℝ)) * r1 ^ j) := by
    have hpoint (j : ℕ) : (a + b * (j : ℝ)) * r1 ^ j =
        a * r1 ^ j + b * ((j : ℝ) * r1 ^ j) := by ring
    have heq : (fun j : ℕ => (a + b * (j : ℝ)) * r1 ^ j) =
        fun j : ℕ => a * r1 ^ j + b * ((j : ℝ) * r1 ^ j) := by
      funext j
      exact hpoint j
    rw [heq]
    exact (hgeo1.summable.mul_left a).add (hlinear1.summable.mul_left b)
  have hbaseSummable : Summable (fun j : ℕ => baseCoeff * r0 ^ j) :=
    hgeo0.summable.mul_left baseCoeff
  have hnonlinearSummable : Summable (fun j : ℕ =>
      nonlinearCoeff * (a + b * (j : ℝ)) * r1 ^ j) := by
    simpa only [mul_assoc] using hpolySummable.mul_left nonlinearCoeff
  have hmajorSummable : Summable majorant := by
    simpa only [majorant] using hbaseSummable.add hnonlinearSummable
  have hpow12eq : (3 : ℝ) ^ (2 * gamma) * (3 : ℝ) ^ (10 * gamma) =
      (3 : ℝ) ^ (12 * gamma) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hpow48eq : (3 : ℝ) ^ (2 * gamma) * (3 : ℝ) ^ (46 * gamma) =
      (3 : ℝ) ^ (48 * gamma) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hpointwise (j : ℕ) : beta ^ j *
      mainRawShellOldFrameP20Control M h m j ≤ majorant j := by
    let q : ℤ := m - ((5 + j : ℕ) : ℤ)
    let s : ℕ := 6 + j
    let J : ℤ := q + (s : ℤ)
    have hJ : J = m + 1 := by dsimp [J, q, s]; omega
    have hqs : q + (s : ℤ) = m + 1 := hJ
    have hstate : nativeInductionState M h m := hpast m le_rfl
    have hvariance := main_rawShell_fixed_old_frame_p20_shell_variance_clock
      M h m q s hqs hstate
    have hV : (q3ModelAmplitude M h (m + 1)) ^ 2 /
        (Annealed.sigmaBar M m : ℝ) ^ 2 ≤
          (9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma) := by
      simpa only [hqs, gamma] using hvariance
    have hlinear := main_rawShell_fixed_old_frame_p20_control_decay_bound M h m j
    let C := rawTraceOldFrameP20LocalClock gamma (6 + j)
    let F := rawTraceOldFrameP20FullResponseCap gamma (6 + j)
    have hCformula : C = (3 : ℝ) ^ (10 * gamma) *
        ((3 : ℝ) ^ (2 * gamma)) ^ j := by
      dsimp [C, rawTraceOldFrameP20LocalClock]
      have hs : ((6 + j : ℕ) : ℝ) = 6 + (j : ℝ) := by push_cast; ring
      rw [hs]
      have hexp : 2 * gamma * (6 + (j : ℝ) - 1) =
          10 * gamma + (2 * gamma) * (j : ℝ) := by ring
      rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    have hcoef : (2018618 : ℝ) / 1000000 + gamma *
        (32474 * ((j + 7 : ℕ) : ℝ) + 11483216) = a + b * (j : ℝ) := by
      dsimp [a, b, gamma, mainRawA, mainRawS]
      push_cast
      ring
    have hprod : C ^ 2 * F =
        4 * (a + b * (j : ℝ)) * (3 : ℝ) ^ (46 * gamma) *
          ((3 : ℝ) ^ (8 * gamma)) ^ j := by
      calc
        _ = 4 * ((2018618 : ℝ) / 1000000 + M.gamma *
            (32474 * ((j + 7 : ℕ) : ℝ) + 11483216)) *
            (3 : ℝ) ^ (46 * M.gamma) * ((3 : ℝ) ^ (8 * M.gamma)) ^ j := by
          dsimp [C, F, gamma]
          exact main_rawShell_old_frame_p20_clock_response_product M.gamma j
        _ = _ := by rw [hcoef]
    have hcontrol : mainRawShellOldFrameP20Control M h m j ≤
        ((9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma)) *
          (120 * C + (1 / 20 : ℝ) * (1 / 9 : ℝ) ^ j * C ^ 2 * F) := by
      have hbrace : 0 ≤ 120 * C + (1 / 20 : ℝ) * (1 / 9 : ℝ) ^ j * C ^ 2 * F := by
        dsimp [C, F, rawTraceOldFrameP20LocalClock,
          rawTraceOldFrameP20FullResponseCap]
        positivity
      calc
        _ ≤ ((q3ModelAmplitude M h (m + 1)) ^ 2 /
              (Annealed.sigmaBar M m : ℝ) ^ 2) *
              (120 * C + (1 / 20 : ℝ) * (1 / 9 : ℝ) ^ j * C ^ 2 * F) := by
          simpa only [C, F, gamma] using hlinear
        _ ≤ _ := mul_le_mul_of_nonneg_right hV hbrace
    have hscaledProd : (1 / 20 : ℝ) * (1 / 9 : ℝ) ^ j * C ^ 2 * F =
        (1 / 5 : ℝ) * (a + b * (j : ℝ)) *
          (3 : ℝ) ^ (46 * gamma) * (((3 : ℝ) ^ (8 * gamma)) ^ j * (1 / 9 : ℝ) ^ j) := by
      calc _ = (1 / 20 : ℝ) * (1 / 9 : ℝ) ^ j * (C ^ 2 * F) := by ring
        _ = _ := by rw [hprod]; ring
    have hbaseTerm : beta ^ j *
        ((9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma) *
          (120 * ((3 : ℝ) ^ (10 * gamma) *
            ((3 : ℝ) ^ (2 * gamma)) ^ j))) =
        540 * gamma * (3 : ℝ) ^ (12 * gamma) * r0 ^ j := by
      calc
        _ = 540 * gamma * ((3 : ℝ) ^ (2 * gamma) *
            (3 : ℝ) ^ (10 * gamma)) *
            (beta ^ j * ((3 : ℝ) ^ (2 * gamma)) ^ j) := by ring
        _ = 540 * gamma * (3 : ℝ) ^ (12 * gamma) *
            (beta ^ j * ((3 : ℝ) ^ (2 * gamma)) ^ j) := by rw [hpow12eq]
        _ = _ := by rw [← mul_pow]
    have hnonlinearTerm : beta ^ j *
        ((9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma) *
          ((1 / 5 : ℝ) * (a + b * (j : ℝ)) *
            (3 : ℝ) ^ (46 * gamma) * (((3 : ℝ) ^ (8 * gamma)) ^ j * (1 / 9 : ℝ) ^ j))) =
        (9 / 10 : ℝ) * gamma * (3 : ℝ) ^ (48 * gamma) *
          (a + b * (j : ℝ)) * r1 ^ j := by
      calc
        _ = (9 / 10 : ℝ) * gamma *
            ((3 : ℝ) ^ (2 * gamma) * (3 : ℝ) ^ (46 * gamma)) *
            (a + b * (j : ℝ)) *
            (beta ^ j * (((3 : ℝ) ^ (8 * gamma)) ^ j * (1 / 9 : ℝ) ^ j)) := by ring
        _ = (9 / 10 : ℝ) * gamma * (3 : ℝ) ^ (48 * gamma) *
            (a + b * (j : ℝ)) *
            (beta ^ j * (((3 : ℝ) ^ (8 * gamma)) ^ j * (1 / 9 : ℝ) ^ j)) := by rw [hpow48eq]
        _ = _ := by
          dsimp [r1]
          rw [mul_pow, mul_pow]
          ring
    have hnonneg : 0 ≤ beta ^ j := pow_nonneg hbeta0 j
    calc
      _ ≤ beta ^ j * (((9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma)) *
          (120 * C + (1 / 20 : ℝ) * (1 / 9 : ℝ) ^ j * C ^ 2 * F)) :=
            mul_le_mul_of_nonneg_left hcontrol hnonneg
      _ = beta ^ j * (((9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma) *
          (120 * C)) + ((9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma) *
          ((1 / 20 : ℝ) * (1 / 9 : ℝ) ^ j * C ^ 2 * F))) := by ring
      _ = majorant j := by
        dsimp only [majorant, baseCoeff, nonlinearCoeff]
        rw [hscaledProd, hCformula]
        rw [mul_add]
        calc
          _ = (beta ^ j * ((9 / 2 : ℝ) * gamma *
                (3 : ℝ) ^ (2 * gamma) *
                (120 * ((3 : ℝ) ^ (10 * gamma) *
                  ((3 : ℝ) ^ (2 * gamma)) ^ j)))) +
              (beta ^ j * ((9 / 2 : ℝ) * gamma *
                (3 : ℝ) ^ (2 * gamma) *
                ((1 / 5 : ℝ) * (a + b * (j : ℝ)) *
                  (3 : ℝ) ^ (46 * gamma) *
                  (((3 : ℝ) ^ (8 * gamma)) ^ j * (1 / 9 : ℝ) ^ j)))) := by ring
          _ = _ := by rw [hbaseTerm, hnonlinearTerm]
  have hnonneg (j : ℕ) : 0 ≤ beta ^ j *
      mainRawShellOldFrameP20Control M h m j :=
    mul_nonneg (pow_nonneg hbeta0 j)
      (main_rawShell_fixed_old_frame_p20_control_admissible M h m j).1
  have hcontrolSummable : Summable (fun j : ℕ => beta ^ j *
      mainRawShellOldFrameP20Control M h m j) :=
    Summable.of_nonneg_of_le hnonneg hpointwise hmajorSummable
  have hpolySum : ∑' j : ℕ, (a + b * (j : ℝ)) * r1 ^ j =
      a / (1 - r1) + b * (r1 / (1 - r1) ^ 2) := by
    calc
      _ = ∑' j : ℕ, (a * r1 ^ j + b * ((j : ℝ) * r1 ^ j)) := by
        apply tsum_congr
        intro j
        ring
      _ = (∑' j : ℕ, a * r1 ^ j) +
          (∑' j : ℕ, b * ((j : ℝ) * r1 ^ j)) :=
        (hgeo1.summable.mul_left a).tsum_add
          (hlinear1.summable.mul_left b)
      _ = _ := by
        rw [tsum_mul_left, hgeo1.tsum_eq, tsum_mul_left, hlinear1.tsum_eq]
        ring
  have hsumMajorant : ∑' j : ℕ, majorant j =
      baseCoeff / (1 - r0) + nonlinearCoeff *
        (a / (1 - r1) + b * (r1 / (1 - r1) ^ 2)) := by
    calc
      _ = (∑' j : ℕ, baseCoeff * r0 ^ j) +
          (∑' j : ℕ, nonlinearCoeff * (a + b * (j : ℝ)) * r1 ^ j) := by
            dsimp [majorant]
            exact hbaseSummable.tsum_add hnonlinearSummable
      _ = _ := by
        rw [tsum_mul_left, hgeo0.tsum_eq]
        have hn : (∑' j : ℕ,
            nonlinearCoeff * (a + b * (j : ℝ)) * r1 ^ j) =
            nonlinearCoeff * (∑' j : ℕ,
              (a + b * (j : ℝ)) * r1 ^ j) := by
          rw [show (fun j : ℕ => nonlinearCoeff *
              (a + b * (j : ℝ)) * r1 ^ j) =
              fun j : ℕ => nonlinearCoeff * ((a + b * (j : ℝ)) * r1 ^ j) by
                funext j
                ring,
            tsum_mul_left]
        rw [hn, hpolySum]
        ring
  refine ⟨hcontrolSummable, ?_⟩
  have hsumC : (1 - alpha) * (∑' j : ℕ, beta ^ j * mainRawShellOldFrameP20Control M h m j) ≤
      (1 - alpha) * (∑' j : ℕ, majorant j) :=
    mul_le_mul_of_nonneg_left (hcontrolSummable.tsum_le_tsum hpointwise hmajorSummable) hweight.1
  refine hsumC.trans (le_of_eq ?_)
  rw [hsumMajorant]
  dsimp only [baseCoeff, nonlinearCoeff, r0, r1, a, b, alpha, beta, gamma]
  unfold mainDeltaH35
  rfl

end ASDExplicitGamma.Main
