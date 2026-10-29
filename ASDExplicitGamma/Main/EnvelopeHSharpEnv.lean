module

public import ASDExplicitGamma.Main.EnvelopeHSharpSum
public import ASDExplicitGamma.Main.EnvelopeHMaxHistory
public import ASDExplicitGamma.Inverse.HistoryBuffer
public import ASDExplicitGamma.Inverse.HistoryMonotoneLp

/-! MA-ENVELOPE-H. The ordinary max history is bounded in `L²` by
`mainEnvelopeH35 v γ t`, the envelope with the provable slope `δ'_H`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Set Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Inverse
  ASDExplicitGamma.Cold ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped ENNReal

noncomputable section

/-- The envelope: `mainEnvelopeH` with the provable slope `δ'_H`. -/
noncomputable def mainEnvelopeH35 (v gamma t : ℝ) : ℝ :=
  (Real.sqrt (mainH0 + mainDeltaH35 gamma * t) + Real.sqrt (2 * v * t) *
    ((3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
      (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld)) ^ 2

private theorem main_ordinary_trace_max_old_profile_bound'
    (M : ABKModel 2) (m : ℤ) (hgamma : M.gamma ≤ gammaZero)
    (hstrong : strong20 M m ≤
      ENNReal.ofReal ((2379 / 2500 : ℝ) * theta M)) :
    Summable (fun j : ℕ => coldHistoryBeta ^ j *
      lpNorm (rawDepthFourLoadTrace M m
        (m - ((5 + j : ℕ) : ℤ)) 0)
        20 (Cutoff.cutoffSampleLaw M).toMeasure) ∧
    (1 - mainAlpha) * ∑' j : ℕ, coldHistoryBeta ^ j *
      lpNorm (rawDepthFourLoadTrace M m
        (m - ((5 + j : ℕ) : ℤ)) 0)
        20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ mainH0 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let B : ℕ → ℝ := fun j => lpNorm
    (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) 0) 20 μ
  have htheta : theta M ≤ 1 := cold_theta_le_one M hgamma
  have hcap : strong20 M m ≤ ENNReal.ofReal (2379 / 2500 : ℝ) := by
    apply hstrong.trans
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have hstrongSum := cold_native_strong_sum
    (show 0 ≤ (2379 / 2500 : ℝ) by norm_num) hcap
  have hinj : Function.Injective (fun j : ℕ => j + 5) := by
    intro a b hab
    exact Nat.add_right_cancel hab
  have htailSummable : Summable (fun j : ℕ =>
      coldNativeStrongRealTerm M m (j + 5)) :=
    hstrongSum.1.comp_injective hinj
  have hBnonneg (j : ℕ) : 0 ≤ B j := lpNorm_nonneg
  have hterm (j : ℕ) : coldNativeStrongRealTerm M m (j + 5) =
      (1 - mainAlpha) * (coldHistoryBeta ^ (j + 5) * B j) := by
    rw [coldNativeStrongRealTerm]
    have hAlpha : coldHistoryAlpha = mainAlpha := by rfl
    rw [hAlpha]
    have hscale : m - ((j + 5 : ℕ) : ℤ) = m - ((5 + j : ℕ) : ℤ) := by
      omega
    rw [hscale, ← main_rawDepthFourLoadTrace_lpNorm_twenty_zero_eq_cutoff]
    change (1 - mainAlpha) * coldHistoryBeta ^ (j + 5) *
      lpNorm (rawDepthFourLoadTrace M m
        (m - ((5 + j : ℕ) : ℤ)) 0) 20 μ =
      (1 - mainAlpha) * (coldHistoryBeta ^ (j + 5) *
        lpNorm (rawDepthFourLoadTrace M m
          (m - ((5 + j : ℕ) : ℤ)) 0) 20 μ)
    ring
  have hAlphaLt : mainAlpha < 1 := by
    dsimp [mainAlpha]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hweightedTail : Summable (fun j : ℕ =>
      (1 - mainAlpha) * (coldHistoryBeta ^ (j + 5) * B j)) := by
    simpa only [hterm] using htailSummable
  have hweightPos : 0 < (1 - mainAlpha) * coldHistoryBeta ^ 5 :=
    mul_pos (sub_pos.mpr hAlphaLt) (pow_pos coldHistoryBeta_pos 5)
  have hprofile : Summable (fun j : ℕ => coldHistoryBeta ^ j * B j) := by
    have heq : (fun j : ℕ =>
        (1 - mainAlpha) * (coldHistoryBeta ^ (j + 5) * B j)) =
        fun j => ((1 - mainAlpha) * coldHistoryBeta ^ 5) *
          (coldHistoryBeta ^ j * B j) := by
      funext j
      rw [pow_add]
      ring
    rw [heq] at hweightedTail
    exact (summable_mul_left_iff hweightPos.ne').mp hweightedTail
  have htailEq : (∑' j : ℕ, coldNativeStrongRealTerm M m (j + 5)) =
      ((1 - mainAlpha) * coldHistoryBeta ^ 5) *
        (∑' j : ℕ, coldHistoryBeta ^ j * B j) := by
    calc
      _ = ∑' j : ℕ,
          ((1 - mainAlpha) * coldHistoryBeta ^ 5) *
            (coldHistoryBeta ^ j * B j) := by
              apply tsum_congr
              intro j
              rw [hterm, pow_add]
              ring
      _ = _ := tsum_mul_left
  have hsumShift := hstrongSum.1.sum_add_tsum_nat_add 5
  have hAlphaOne : mainAlpha ≤ 1 := by
    dsimp [mainAlpha]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hprefix : 0 ≤ ∑ r ∈ Finset.range 5,
      coldNativeStrongRealTerm M m r := by
    apply Finset.sum_nonneg
    intro r hr
    simp only [coldNativeStrongRealTerm]
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hAlphaOne)
        (pow_nonneg coldHistoryBeta_pos.le r)) lpNorm_nonneg
  have htailLe : (∑' j : ℕ, coldNativeStrongRealTerm M m (j + 5)) ≤
      ∑' r : ℕ, coldNativeStrongRealTerm M m r := by
    linarith [hsumShift]
  let C : ℝ := (coldHistoryBeta ^ 5)⁻¹
  have hCpos : 0 < C := inv_pos.mpr (pow_pos coldHistoryBeta_pos 5)
  have hprofileBound : (1 - mainAlpha) *
      (∑' j : ℕ, coldHistoryBeta ^ j * B j) ≤ mainH0 := by
    calc
      _ = C * ((1 - mainAlpha) * coldHistoryBeta ^ 5 *
          (∑' j : ℕ, coldHistoryBeta ^ j * B j)) := by
            dsimp [C]
            have hcancel : (coldHistoryBeta ^ 5)⁻¹ * coldHistoryBeta ^ 5 = 1 :=
              inv_mul_cancel₀ (ne_of_gt (pow_pos coldHistoryBeta_pos 5))
            calc
              _ = (1 - mainAlpha) *
                    ((coldHistoryBeta ^ 5)⁻¹ * coldHistoryBeta ^ 5) *
                    (∑' j : ℕ, coldHistoryBeta ^ j * B j) := by rw [hcancel]; ring
              _ = _ := by ring
      _ = C * (∑' j : ℕ, coldNativeStrongRealTerm M m (j + 5)) := by
            rw [← htailEq]
      _ ≤ C * (∑' r : ℕ, coldNativeStrongRealTerm M m r) :=
            mul_le_mul_of_nonneg_left htailLe hCpos.le
      _ ≤ C * (2379 / 2500 : ℝ) :=
            mul_le_mul_of_nonneg_left hstrongSum.2 hCpos.le
      _ = mainH0 := by
            dsimp [C]
            have hbeta : coldHistoryBeta ^ 5 = (3 : ℝ) ^ (-(3 / 4 : ℝ)) := by
              rw [cold_native_beta_power]
              congr 1
              norm_num
            have hinv : (coldHistoryBeta ^ 5)⁻¹ = (3 : ℝ) ^ (3 / 4 : ℝ) := by
              rw [hbeta, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) (3 / 4 : ℝ)]
              simp
            rw [hinv, mainH0]
  exact ⟨by simpa only [B] using hprofile, by simpa only [B] using hprofileBound⟩

private theorem main_max_history_population_weight' (j : ℕ) :
    ENNReal.ofReal (mainAlpha ^ j) *
        ((9 : ℝ≥0∞) ^ j) ^ (1 / 20 : ℝ) =
      ENNReal.ofReal (mainBetaPrime ^ j) := by
  have hAlpha : mainAlpha ^ j = (3 : ℝ) ^ (-(1 / 4 : ℝ) * (j : ℝ)) := by
    rw [mainAlpha, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
  have hBeta : mainBetaPrime ^ j = (3 : ℝ) ^ (-(3 / 20 : ℝ) * (j : ℝ)) := by
    rw [mainBetaPrime, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
  rw [hAlpha, hBeta]
  exact history_population_weight j

/-- The actual fixed-frame p=20 generator controls each OLD depth trace from
its zero-insertion profile. -/
private theorem main_rawDepth_lpNorm_twenty_bound_of_fixed_old_frame_control'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (hstrong : strong20 M m ≤
      ENNReal.ofReal ((2379 / 2500 : ℝ) * theta M))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (j : ℕ) :
    lpNorm (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) t)
        20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      lpNorm (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) 0)
        20 (Cutoff.cutoffSampleLaw M).toMeasure +
      t * mainRawShellOldFrameP20Control M h m j := by
  let q : ℤ := m - ((5 + j : ℕ) : ℤ)
  let Q : TriadicCube 2 := originCube 2 q
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let U : ℝ → ℝ := fun _ => mainRawShellOldFrameP20Control M h m j
  have hU0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ U s := by
    intro s hs
    simpa only [U] using
      (main_rawShell_fixed_old_frame_p20_control_admissible M h m j).1
  have hUInt : IntegrableOn U (Icc (0 : ℝ) 1) := by
    simpa only [U] using
      (main_rawShell_fixed_old_frame_p20_control_admissible M h m j).2
  have hT0 : MemLp (rawDepthFourLoadTrace M m q 0) 20 μ := by
    simpa only [q] using
      main_rawDepthFourLoadTrace_memLp_twenty_zero_of_strong20 M m _ hstrong j
  have hTt : MemLp (rawDepthFourLoadTrace M m q t) 20 μ := by
    simpa only [q] using
      main_rawDepthFourLoadTrace_memLp_twenty_fixed_old_frame
        M h hM hgamma m hpast j t ⟨ht0, ht1⟩
  have hGenerator : ∀ s ∈ Ioo (0 : ℝ) 1,
      deriv (modelTracePowerHeatAverage q M m 20) s ≤
        20 * modelTracePowerHeatAverage q M m 20 s ^ ((19 : ℝ) / 20) * U s := by
    intro s hs
    simpa only [U, q] using
      (main_rawShell_fixed_old_frame_p20_hGenerator M h hM hgamma m hpast j) s hs
  have hB : lpNorm (rawDepthFourLoadTrace M m q 0) 20 μ ≤
      lpNorm (rawDepthFourLoadTrace M m q 0) 20 μ := le_rfl
  have hcube := main_rawCube_lpNorm_twenty_bound_of_generator
    Q M h hM m U (fun s hs => hU0 s hs) hUInt t ht0 ht1 hGenerator
    hT0 hTt _ hB
  have hcubeEq := main_rawCubeFourLoadTrace_lpNorm_eq_origin M m Q t 20 hTt
  have hint : ∫ s in (0 : ℝ)..t, U s =
      t * mainRawShellOldFrameP20Control M h m j := by
    simp [U, intervalIntegral.integral_const]
  simpa only [q] using calc
    lpNorm (rawDepthFourLoadTrace M m q t) 20 μ =
        lpNorm (rawCubeFourLoadTrace M m Q t) 20 μ := hcubeEq.symm
    _ ≤ lpNorm (rawDepthFourLoadTrace M m q 0) 20 μ +
        ∫ s in (0 : ℝ)..t, U s := hcube
    _ = lpNorm (rawDepthFourLoadTrace M m q 0) 20 μ +
        t * mainRawShellOldFrameP20Control M h m j := by rw [hint]

private theorem main_ordinary_trace_max_history_eLpNorm_twenty_le_source'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eLpNorm (mainOrdinaryTraceMaxHistory M m
      (originCube 2 (m - 5)) t)
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (mainH0 + mainDeltaH35 M.gamma * t) := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hstate : nativeInductionState M h m := hpast m le_rfl
  have hstrong : strong20 M m ≤
      ENNReal.ofReal ((2379 / 2500 : ℝ) * theta M) := hstate.2.1
  let B : ℕ → ℝ := fun j => lpNorm
    (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) 0) 20 μ
  let C : ℕ → ℝ := fun j => mainRawShellOldFrameP20Control M h m j
  let g : ℕ → ℝ := fun j => mainBetaPrime ^ j * (B j + t * C j)
  let F : ℕ → Cutoff.CutoffSample 2 → ℝ≥0∞ := fun j ω =>
    ENNReal.ofReal (mainAlpha ^ j) * mainOrdinaryTraceDepthMax M m Q t j ω
  have hB := main_ordinary_trace_max_old_profile_bound' M m hgamma hstrong
  have hbeta : mainBetaPrime = coldHistoryBeta := by rfl
  have hBsum : Summable (fun j : ℕ => mainBetaPrime ^ j * B j) := by
    simpa only [B, hbeta] using hB.1
  have hBbound : (1 - mainAlpha) *
      ∑' j : ℕ, mainBetaPrime ^ j * B j ≤ mainH0 := by
    simpa only [B, hbeta] using hB.2
  have hC := main_rawShell_fixed_old_frame_p20_control_beta_discounted_le_deltaH35
    M h hgamma m hpast
  have hCsum : Summable (fun j : ℕ => mainBetaPrime ^ j * C j) := by
    simpa only [C] using hC.1
  have hBeta0 : 0 ≤ mainBetaPrime := by
    dsimp [mainBetaPrime]
    positivity
  have hGnonneg (j : ℕ) : 0 ≤ g j := by
    dsimp [g]
    exact mul_nonneg (pow_nonneg hBeta0 j)
      (add_nonneg lpNorm_nonneg (mul_nonneg ht0
        (main_rawShell_fixed_old_frame_p20_control_admissible M h m j).1))
  have hGsum : Summable g := by
    have heq : g = fun j : ℕ =>
        mainBetaPrime ^ j * B j + t * (mainBetaPrime ^ j * C j) := by
      funext j
      dsimp [g]
      ring
    rw [heq]
    exact hBsum.add (hCsum.mul_left t)
  have hsplit : (∑' j : ℕ, g j) =
      (∑' j : ℕ, mainBetaPrime ^ j * B j) +
        t * (∑' j : ℕ, mainBetaPrime ^ j * C j) := by
    calc
      _ = ∑' j : ℕ,
          (mainBetaPrime ^ j * B j + t * (mainBetaPrime ^ j * C j)) := by
            apply tsum_congr
            intro j
            dsimp [g]
            ring
      _ = (∑' j : ℕ, mainBetaPrime ^ j * B j) +
          ∑' j : ℕ, t * (mainBetaPrime ^ j * C j) :=
        hBsum.tsum_add (hCsum.mul_left t)
      _ = _ := by rw [tsum_mul_left]
  have hweightBound : (1 - mainAlpha) * (∑' j : ℕ, g j) ≤
      mainH0 + mainDeltaH35 M.gamma * t := by
    have hAlphaLt : mainAlpha < 1 := by
      dsimp [mainAlpha]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    rw [hsplit]
    calc
      _ = (1 - mainAlpha) * (∑' j : ℕ, mainBetaPrime ^ j * B j) +
          t * ((1 - mainAlpha) *
            (∑' j : ℕ, mainBetaPrime ^ j * C j)) := by ring
      _ ≤ mainH0 + t * (mainDeltaH35 M.gamma) :=
        add_le_add hBbound (mul_le_mul_of_nonneg_left hC.2 ht0)
      _ = _ := by ring
  have hFmeas (j : ℕ) : Measurable (F j) := by
    dsimp [F]
    exact (main_ordinary_trace_depth_max_measurable M m Q t j).const_mul _
  have hFbound (j : ℕ) :
      eLpNorm (F j) 20 μ ≤ ENNReal.ofReal (g j) := by
    have hraw := main_rawDepth_lpNorm_twenty_bound_of_fixed_old_frame_control'
      M h hM hgamma m hpast hstrong t ht0 ht1 j
    have hdepth := main_ordinary_trace_depth_max_L20_bound
      M h hM hgamma m hpast t ht0 ht1 j
    have hscale : 0 ≤ mainAlpha ^ j := pow_nonneg
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) j
    have hbetaPow : 0 ≤ mainBetaPrime ^ j := pow_nonneg hBeta0 j
    have hpop := main_max_history_population_weight' j
    change eLpNorm (fun ω => ENNReal.ofReal (mainAlpha ^ j) *
        mainOrdinaryTraceDepthMax M m Q t j ω) 20 μ ≤ _
    rw [history_constant_mul_L20 μ (ENNReal.ofReal (mainAlpha ^ j))
      (mainOrdinaryTraceDepthMax M m Q t j)
      (main_ordinary_trace_depth_max_measurable M m Q t j)]
    calc
      _ ≤ ENNReal.ofReal (mainAlpha ^ j) *
          (((9 : ℝ≥0∞) ^ j) ^ (1 / 20 : ℝ) *
            ENNReal.ofReal (lpNorm
              (rawDepthFourLoadTrace M m
                (m - ((5 + j : ℕ) : ℤ)) t) 20 μ)) :=
        mul_le_mul_of_nonneg_left hdepth (by positivity)
      _ = (ENNReal.ofReal (mainBetaPrime ^ j)) *
          ENNReal.ofReal (lpNorm
            (rawDepthFourLoadTrace M m
              (m - ((5 + j : ℕ) : ℤ)) t) 20 μ) := by
        rw [← mul_assoc, hpop]
      _ ≤ ENNReal.ofReal (mainBetaPrime ^ j) *
          ENNReal.ofReal (B j + t * C j) := by
        exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hraw)
          (by positivity)
      _ = ENNReal.ofReal (g j) := by
        rw [← ENNReal.ofReal_mul hbetaPow]
  have hFseries := history_ennreal_tsum_L20 μ F hFmeas
  have hsumBound : (∑' j : ℕ, eLpNorm (F j) 20 μ) ≤
      ENNReal.ofReal (∑' j : ℕ, g j) := by
    calc
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (g j) :=
        ENNReal.tsum_le_tsum hFbound
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg hGnonneg hGsum).symm
  have hscaleHistory :
      mainOrdinaryTraceMaxHistory M m Q t = fun ω =>
        ENNReal.ofReal (1 - mainAlpha) * ∑' j : ℕ, F j ω := by
    funext ω
    simp [mainOrdinaryTraceMaxHistory, F, mainOrdinaryTraceDepthMax]
  have hfactor0 : 0 ≤ 1 - mainAlpha := by
    dsimp [mainAlpha]
    exact sub_nonneg.mpr
      (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num))
  have hseriesMeas : Measurable (fun ω => ∑' j : ℕ, F j ω) :=
    Measurable.tsum hFmeas
  calc
    _ = eLpNorm (fun ω =>
          ENNReal.ofReal (1 - mainAlpha) * ∑' j : ℕ, F j ω) 20 μ := by
        rw [hscaleHistory]
    _ = ENNReal.ofReal (1 - mainAlpha) *
          eLpNorm (fun ω => ∑' j : ℕ, F j ω) 20 μ :=
        history_constant_mul_L20 μ _ _ hseriesMeas
    _ ≤ ENNReal.ofReal (1 - mainAlpha) *
          (∑' j : ℕ, eLpNorm (F j) 20 μ) :=
        mul_le_mul_of_nonneg_left hFseries (by positivity)
    _ ≤ ENNReal.ofReal (1 - mainAlpha) * ENNReal.ofReal (∑' j : ℕ, g j) :=
        mul_le_mul_of_nonneg_left hsumBound (by positivity)
    _ = ENNReal.ofReal ((1 - mainAlpha) * (∑' j : ℕ, g j)) :=
        (ENNReal.ofReal_mul hfactor0).symm
    _ ≤ ENNReal.ofReal (mainH0 + mainDeltaH35 M.gamma * t) :=
        ENNReal.ofReal_le_ofReal hweightBound

theorem main_ordinary_trace_max_history_memLp_two_le_mainEnvelopeH35
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) t ω < ⊤) ∧
    MemLp
      (fun ω => (mainOrdinaryTraceMaxHistory M m
        (originCube 2 (m - 5)) t ω).toReal)
      2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
    lpNorm
      (fun ω => (mainOrdinaryTraceMaxHistory M m
        (originCube 2 (m - 5)) t ω).toReal)
      2 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t := by
  let H := mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) t
  let T : Cutoff.CutoffSample 2 → ℝ := fun ω => (H ω).toReal
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hstate : nativeInductionState M h m := hpast m le_rfl
  have hstrong : strong20 M m ≤
      ENNReal.ofReal ((2379 / 2500 : ℝ) * theta M) := hstate.2.1
  have hHmeas : Measurable H := by
    dsimp [H]
    exact main_ordinary_trace_max_history_measurable M m
      (originCube 2 (m - 5)) t
  have hsource := main_ordinary_trace_max_history_eLpNorm_twenty_le_source'
    M h hM hgamma m hpast t ht0 ht1
  have hδ0 : 0 ≤ mainDeltaH35 M.gamma := by
    have hC := main_rawShell_fixed_old_frame_p20_control_beta_discounted_le_deltaH35
      M h hgamma m hpast
    have hnn : 0 ≤ (1 - mainAlpha) * ∑' j : ℕ, mainBetaPrime ^ j *
        mainRawShellOldFrameP20Control M h m j := by
      refine mul_nonneg ?_ (tsum_nonneg fun j => mul_nonneg ?_
        (main_rawShell_fixed_old_frame_p20_control_admissible M h m j).1)
      · dsimp [mainAlpha]
        exact sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num))
      · dsimp [mainBetaPrime]; positivity
    exact hnn.trans hC.2
  have hEnvelope : mainH0 + mainDeltaH35 M.gamma * t ≤ mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t := by
    have hH00 : 0 ≤ mainH0 := by unfold mainH0; positivity
    have hrad : 0 ≤ mainH0 + mainDeltaH35 M.gamma * t := by
      have := mul_nonneg hδ0 ht0
      linarith
    set A := Real.sqrt (mainH0 + mainDeltaH35 M.gamma * t) with hA
    have hAsq : A ^ 2 = mainH0 + mainDeltaH35 M.gamma * t := Real.sq_sqrt hrad
    have hB : 0 ≤ Real.sqrt (2 * ((q3ModelAmplitude M h (m + 1) /
        (Annealed.sigmaBar M m : ℝ)) ^ 2) * t) *
        ((3 : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt mainBetaOld +
          (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld) := by positivity
    have hA0 : 0 ≤ A := Real.sqrt_nonneg _
    unfold mainEnvelopeH35
    nlinarith [hAsq, mul_nonneg hA0 hB]
  have hEnvelope0 : 0 ≤ mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t := by
    dsimp [mainEnvelopeH35]
    positivity
  have hH20 : eLpNorm H 20 μ ≤
      ENNReal.ofReal (mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t) := by
    calc
      _ ≤ ENNReal.ofReal (mainH0 + mainDeltaH35 M.gamma * t) := hsource
      _ ≤ _ := ENNReal.ofReal_le_ofReal hEnvelope
  have hH2 : eLpNorm H 2 μ ≤
      ENNReal.ofReal (mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t) := by
    exact (eLpNorm_le_eLpNorm_of_exponent_le
      (by norm_num : (2 : ℝ≥0∞) ≤ 20)).trans hH20
  have hMoment : (∫⁻ ω, (H ω) ^ 20 ∂μ) ≠ ⊤ := by
    rw [← history_L20_power μ H hHmeas]
    exact ne_top_of_le_ne_top (by simp)
      (pow_le_pow_left' hH20 20)
  have hHpowFinite : ∀ᵐ ω ∂μ, (H ω) ^ 20 < ⊤ :=
    ae_lt_top (hHmeas.pow_const 20) hMoment
  have hfinite : ∀ᵐ ω ∂μ, H ω < ⊤ := by
    filter_upwards [hHpowFinite] with ω hω
    by_contra htop
    have htop' : H ω = ⊤ := by simpa using htop
    simp only [htop', ENNReal.top_pow (by norm_num : (20 : ℕ) ≠ 0), lt_self_iff_false]
      at hω
  have hTnonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ T ω := by
    dsimp [T]
    exact ENNReal.toReal_nonneg
  have hTnorm : eLpNorm T 2 μ = eLpNorm H 2 μ := by
    calc
      _ = eLpNorm (fun ω => ENNReal.ofReal (T ω)) 2 μ := by
        symm
        exact eLpNorm_ofReal T (Filter.Eventually.of_forall hTnonneg)
      _ = _ := eLpNorm_congr_ae (ofReal_toReal_ae_eq hfinite)
  have hTmem : MemLp T 2 μ := by
    rw [memLp_iff, hTnorm]
    exact lt_of_le_of_lt hH2 ENNReal.ofReal_lt_top
  have hTbound : lpNorm T 2 μ ≤ mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t := by
    change (eLpNorm T 2 μ).toReal ≤ mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t
    rw [hTnorm]
    calc
      _ ≤ (ENNReal.ofReal (mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hH2
      _ = mainEnvelopeH35 ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma t := ENNReal.toReal_ofReal hEnvelope0
  refine ⟨hfinite, ?_, ?_⟩
  · simpa only [T, H] using hTmem
  · simpa only [T, H] using hTbound

end

end ASDExplicitGamma.Main
