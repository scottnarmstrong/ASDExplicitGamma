module

public import ASDExplicitGamma.Main.EnvelopeHControlComparison
public import ASDExplicitGamma.Inverse.HistoryBuffer
public import ASDExplicitGamma.Inverse.HistoryMonotoneLp

/-! The max-based OLD trace history, with order-20 population payment. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Set Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Inverse
  ASDExplicitGamma.Cold ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped ENNReal

noncomputable section

/-- The source `T_V` mark for the partial insertion, in its fixed OLD frame. -/
noncomputable def mainOrdinaryTraceDepthMax
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (t : ℝ) (j : ℕ) :
    Cutoff.CutoffSample 2 → ℝ≥0∞ :=
  historyFiniteMax (descendantsAtDepth Q j)
    (fun V ω => ENNReal.ofReal (rawCubeFourLoadTrace M m V t ω))

/-- The complete normalized max-based ordinary trace history `H_U(a_t)`. -/
noncomputable def mainOrdinaryTraceMaxHistory
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - mainAlpha) * ∑' j : ℕ,
    ENNReal.ofReal (mainAlpha ^ j) * mainOrdinaryTraceDepthMax M m Q t j ω

private theorem main_rawDepthFourLoadTrace_measurable
    (M : ABKModel 2) (m q : ℤ) (t : ℝ) :
    Measurable (rawDepthFourLoadTrace M m q t) := by
  let K := closure (cubeSet (originCube 2 q))
  have : CompactSpace K := modelHeatCubeClosureCompact q
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 q)).isCompact_closure
  have hscalar : Measurable (modelInsertedScalar K m t) := by
    change Measurable (fun ω => olderField K m ω +
      Real.sqrt t • shellFieldScalarRestriction K (ω.1 (m + 1)))
    exact (measurable_olderField K ell m hK).add
      (((measurable_shellFieldScalarRestriction K).comp
        ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)).const_smul
          (Real.sqrt t))
  have hobs := (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives q M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1).1.continuous.measurable.comp hscalar
  have heq : rawDepthFourLoadTrace M m q t =
      fun ω => modelTraceObservable q M.nu (Annealed.sigmaBar M m : ℝ)
        (modelInsertedScalar K m t ω) := by
    funext ω
    exact raw_depth_four_load_trace_eq_model_observable M m q t ω
  rw [heq]
  exact hobs

private theorem main_rawCubeFourLoadTrace_measurable
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (t : ℝ) :
    Measurable (rawCubeFourLoadTrace M m Q t) := by
  have heq : rawCubeFourLoadTrace M m Q t =
      fun ω => rawDepthFourLoadTrace M m Q.scale t
        (Cutoff.translateCutoffSample (triadicCubeShift Q) ω) := by
    funext ω
    exact main_rawCubeFourLoadTrace_translate_to_origin M m Q t ω
  rw [heq]
  exact (main_rawDepthFourLoadTrace_measurable M m Q.scale t).comp
    (Cutoff.measurable_translateCutoffSample (triadicCubeShift Q))

theorem main_ordinary_trace_depth_max_measurable
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (t : ℝ) (j : ℕ) :
    Measurable (mainOrdinaryTraceDepthMax M m Q t j) := by
  apply history_finite_max_measurable
  intro V
  exact (main_rawCubeFourLoadTrace_measurable M m V t).ennreal_ofReal

theorem main_ordinary_trace_max_history_measurable
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (t : ℝ) :
    Measurable (mainOrdinaryTraceMaxHistory M m Q t) := by
  unfold mainOrdinaryTraceMaxHistory
  exact (Measurable.tsum (fun j =>
    (main_ordinary_trace_depth_max_measurable M m Q t j).const_mul _)).const_mul _

/-- The actual translated-cell maximum pays exactly `9^(j/20)` in L20. -/
theorem main_ordinary_trace_depth_max_L20_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (j : ℕ) :
    eLpNorm (mainOrdinaryTraceDepthMax M m (originCube 2 (m - 5)) t j)
        20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ((9 : ℝ≥0∞) ^ j) ^ (1 / 20 : ℝ) *
        ENNReal.ofReal (lpNorm
          (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) t)
          20 (Cutoff.cutoffSampleLaw M).toMeasure) := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let s := descendantsAtDepth Q j
  have hOrigin : MemLp
      (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) t) 20 μ := by
    exact main_rawDepthFourLoadTrace_memLp_twenty_fixed_old_frame
      M h hM hgamma m hpast j t ⟨ht0, ht1⟩
  have hcell (V : TriadicCube 2) (hV : V ∈ s) :
      MemLp (rawCubeFourLoadTrace M m V t) 20 μ := by
    have hscale : V.scale = m - ((5 + j : ℕ) : ℤ) := by
      dsimp [s, Q]
      rw [scale_eq_sub_of_mem_descendantsAtDepth hV]
      change (m - 5) - (j : ℤ) = m - ((5 + j : ℕ) : ℤ)
      omega
    have hOriginV : MemLp (rawDepthFourLoadTrace M m V.scale t) 20 μ := by
      simpa only [hscale] using hOrigin
    exact main_rawCubeFourLoadTrace_memLp_of_origin M m V t 20 hOriginV
  have hnorm (V : TriadicCube 2) (hV : V ∈ s) :
      eLpNorm (fun ω => ENNReal.ofReal (rawCubeFourLoadTrace M m V t ω))
          20 μ ≤
        ENNReal.ofReal (lpNorm
          (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) t) 20 μ) := by
    have hnonneg (ω : Cutoff.CutoffSample 2) :
        0 ≤ rawCubeFourLoadTrace M m V t ω :=
      raw_cube_four_load_trace_nonneg M m V t ⟨ht0, ht1⟩ ω
    have hto :
        (fun ω => ENNReal.ofReal (rawCubeFourLoadTrace M m V t ω)) =
          fun ω => ‖rawCubeFourLoadTrace M m V t ω‖ₑ := by
      funext ω
      exact (Real.enorm_eq_ofReal (hnonneg ω)).symm
    rw [hto, eLpNorm_enorm _ (hcell V hV).aestronglyMeasurable]
    apply le_of_eq
    have hscale : V.scale = m - ((5 + j : ℕ) : ℤ) := by
      dsimp [s, Q]
      rw [scale_eq_sub_of_mem_descendantsAtDepth hV]
      change (m - 5) - (j : ℤ) = m - ((5 + j : ℕ) : ℤ)
      omega
    calc
      _ = ENNReal.ofReal
          (lpNorm (rawCubeFourLoadTrace M m V t) 20 μ) := by
            rw [← ENNReal.ofReal_toReal (hcell V hV).eLpNorm_ne_top]
            rfl
      _ = ENNReal.ofReal
          (lpNorm (rawDepthFourLoadTrace M m
            (m - ((5 + j : ℕ) : ℤ)) t) 20 μ) := by
            have hOriginV : MemLp (rawDepthFourLoadTrace M m V.scale t) 20 μ := by
              simpa only [hscale] using hOrigin
            have hnormeq := main_rawCubeFourLoadTrace_lpNorm_eq_origin
              M m V t 20 hOriginV
            simpa only [hscale] using congrArg ENNReal.ofReal hnormeq
  have hmax := history_finite_max_L20 μ s
    (fun V ω => ENNReal.ofReal (rawCubeFourLoadTrace M m V t ω))
    (fun V => (main_rawCubeFourLoadTrace_measurable M m V t).ennreal_ofReal)
    (ENNReal.ofReal (lpNorm
      (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) t) 20 μ)) hnorm
  have hcard : (s.card : ℝ≥0∞) = (9 : ℝ≥0∞) ^ j := by
    dsimp [s]
    rw [descendantsAtDepth_card]
    norm_num
  simpa only [mainOrdinaryTraceDepthMax, Q, hcard] using hmax

/-- The frozen strong20 coordinate controls the old-time max profile after
the exact population factor has changed alpha into beta. -/
private theorem main_ordinary_trace_max_old_profile_bound
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

private theorem main_three_rpow_one_sixteenth_le_four_thirds :
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

private theorem main_three_rpow_neg_one_seventh_le_six_sevenths :
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

/-- The actual fixed-frame generator remains summable after the exact
order-20 population payment changes the history discount from alpha to beta. -/
private theorem main_rawShell_fixed_old_frame_p20_control_beta_discounted_bound
    (M : ABKModel 2) (h : ℝ) (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n) :
    Summable (fun j : ℕ => mainBetaPrime ^ j *
      mainRawShellOldFrameP20Control M h m j) ∧
    (1 - mainAlpha) * ∑' j : ℕ, mainBetaPrime ^ j *
      mainRawShellOldFrameP20Control M h m j ≤ 13000 * M.gamma := by
  let gamma : ℝ := M.gamma
  let alpha : ℝ := mainAlpha
  let beta : ℝ := mainBetaPrime
  let r0 : ℝ := beta * (3 : ℝ) ^ (2 * gamma)
  let r1 : ℝ := beta * (3 : ℝ) ^ (8 * gamma)
  let a : ℝ := mainRawA gamma
  let b : ℝ := mainRawS gamma
  let baseCoeff : ℝ := 540 * gamma * (3 : ℝ) ^ (12 * gamma)
  let nonlinearCoeff : ℝ := (603 / 500 : ℝ) * gamma * (3 : ℝ) ^ (48 * gamma)
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
      main_three_rpow_one_sixteenth_le_four_thirds
  have hpow48 : (3 : ℝ) ^ (48 * gamma) ≤ 4 / 3 := by
    have hexp : 48 * gamma ≤ 1 / 16 := by nlinarith
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp).trans
      main_three_rpow_one_sixteenth_le_four_thirds
  have ha : a ≤ 4000 := by
    dsimp [a, gamma, mainRawA]
    nlinarith [hgamma']
  have hb : b ≤ 12 := by
    dsimp [b, gamma, mainRawS]
    nlinarith [hgamma']
  have hr1eq : r1 = (3 : ℝ) ^ (8 * gamma - 3 / 20) := by
    dsimp [r1, beta, mainBetaPrime]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hr0eq : r0 = (3 : ℝ) ^ (2 * gamma - 3 / 20) := by
    dsimp [r0, beta, mainBetaPrime]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hexpBeta : 8 * gamma - 3 / 20 ≤ -(1 / 7 : ℝ) := by
    norm_num at hgamma'
    norm_num
    nlinarith
  have hr1bound : r1 ≤ 6 / 7 := by
    rw [hr1eq]
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpBeta).trans
      main_three_rpow_neg_one_seventh_le_six_sevenths
  have hbeta0 : 0 ≤ beta := by
    dsimp [beta, mainBetaPrime]
    exact Real.rpow_nonneg (by norm_num) _
  have hr0nonneg : 0 ≤ r0 := by
    dsimp [r0]
    exact mul_nonneg hbeta0 (Real.rpow_nonneg (by norm_num) _)
  have hr1nonneg : 0 ≤ r1 := by
    dsimp [r1]
    exact mul_nonneg hbeta0 (Real.rpow_nonneg (by norm_num) _)
  have hr0le : r0 ≤ r1 := by
    rw [hr0eq, hr1eq]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hgamma0])
  have hr0bound : r0 ≤ 6 / 7 := hr0le.trans hr1bound
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
    have hlinear := main_rawShell_fixed_old_frame_p20_control_linear_clock_bound
      M h m j
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
          (120 * C + (67 / 1000 : ℝ) * C ^ 2 * F) := by
      have hbrace : 0 ≤ 120 * C + (67 / 1000 : ℝ) * C ^ 2 * F := by
        dsimp [C, F, rawTraceOldFrameP20LocalClock,
          rawTraceOldFrameP20FullResponseCap]
        positivity
      have hV' : (q3ModelAmplitude M h (m + 1)) ^ 2 /
          (Annealed.sigmaBar M m : ℝ) ^ 2 =
            (q3ModelAmplitude M h (m + 1)) ^ 2 /
              (Annealed.sigmaBar M m : ℝ) ^ 2 := rfl
      calc
        _ ≤ ((q3ModelAmplitude M h (m + 1)) ^ 2 /
              (Annealed.sigmaBar M m : ℝ) ^ 2) *
              (120 * C + (67 / 1000 : ℝ) * C ^ 2 * F) := by
          simpa only [C, F, gamma] using hlinear
        _ ≤ _ := mul_le_mul_of_nonneg_right hV hbrace
    have hscaledProd : (67 / 1000 : ℝ) * C ^ 2 * F =
        (67 / 250 : ℝ) * (a + b * (j : ℝ)) *
          (3 : ℝ) ^ (46 * gamma) * ((3 : ℝ) ^ (8 * gamma)) ^ j := by
      rw [mul_assoc, hprod]
      ring
    have hbaseTerm : beta ^ j *
        ((9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma) *
          (120 * (3 : ℝ) ^ (10 * gamma) *
            ((3 : ℝ) ^ (2 * gamma)) ^ j)) =
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
          ((67 / 250 : ℝ) * (a + b * (j : ℝ)) *
            (3 : ℝ) ^ (46 * gamma) * ((3 : ℝ) ^ (8 * gamma)) ^ j)) =
        (603 / 500 : ℝ) * gamma * (3 : ℝ) ^ (48 * gamma) *
          (a + b * (j : ℝ)) * r1 ^ j := by
      calc
        _ = (603 / 500 : ℝ) * gamma *
            ((3 : ℝ) ^ (2 * gamma) * (3 : ℝ) ^ (46 * gamma)) *
            (a + b * (j : ℝ)) *
            (beta ^ j * ((3 : ℝ) ^ (8 * gamma)) ^ j) := by ring
        _ = (603 / 500 : ℝ) * gamma * (3 : ℝ) ^ (48 * gamma) *
            (a + b * (j : ℝ)) *
            (beta ^ j * ((3 : ℝ) ^ (8 * gamma)) ^ j) := by rw [hpow48eq]
        _ = _ := by rw [← mul_pow]
    have hnonneg : 0 ≤ beta ^ j := pow_nonneg hbeta0 j
    calc
      _ ≤ beta ^ j * (((9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma)) *
          (120 * C + (67 / 1000 : ℝ) * C ^ 2 * F)) :=
            mul_le_mul_of_nonneg_left hcontrol hnonneg
      _ = beta ^ j * (((9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma) *
          (120 * C)) + ((9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * gamma) *
          ((67 / 1000 : ℝ) * C ^ 2 * F))) := by ring
      _ = majorant j := by
        dsimp [majorant, baseCoeff, nonlinearCoeff, r0, r1]
        rw [hscaledProd, hCformula]
        rw [mul_add]
        calc
          _ = (beta ^ j * ((9 / 2 : ℝ) * gamma *
                (3 : ℝ) ^ (2 * gamma) *
                (120 * (3 : ℝ) ^ (10 * gamma) *
                  ((3 : ℝ) ^ (2 * gamma)) ^ j))) +
              (beta ^ j * ((9 / 2 : ℝ) * gamma *
                (3 : ℝ) ^ (2 * gamma) *
                ((67 / 250 : ℝ) * (a + b * (j : ℝ)) *
                  (3 : ℝ) ^ (46 * gamma) *
                  ((3 : ℝ) ^ (8 * gamma)) ^ j))) := by ring
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
  have hgap0 : 1 / 7 ≤ 1 - r0 := by linarith [hr0bound]
  have hgap1 : 1 / 7 ≤ 1 - r1 := by linarith [hr1bound]
  have hratio0 : (1 - alpha) / (1 - r0) ≤ 7 / 4 := by
    have hden : 0 < 1 - r0 := lt_of_lt_of_le (by norm_num) hgap0
    apply (div_le_iff₀ hden).2
    calc
      _ ≤ 1 / 4 := hweight.2
      _ = (7 / 4 : ℝ) * (1 / 7) := by norm_num
      _ ≤ (7 / 4 : ℝ) * (1 - r0) :=
        mul_le_mul_of_nonneg_left hgap0 (by norm_num)
  have hratio1 : (1 - alpha) / (1 - r1) ≤ 7 / 4 := by
    have hden : 0 < 1 - r1 := lt_of_lt_of_le (by norm_num) hgap1
    apply (div_le_iff₀ hden).2
    calc
      _ ≤ 1 / 4 := hweight.2
      _ = (7 / 4 : ℝ) * (1 / 7) := by norm_num
      _ ≤ (7 / 4 : ℝ) * (1 - r1) :=
        mul_le_mul_of_nonneg_left hgap1 (by norm_num)
  have hratioMoment : r1 / (1 - r1) ^ 2 ≤ 42 := by
    have hden : 0 < (1 - r1) ^ 2 := by positivity
    apply (div_le_iff₀ hden).2
    have hgapSq : (1 / 7 : ℝ) ^ 2 ≤ (1 - r1) ^ 2 := by
      apply pow_le_pow_left₀ (by norm_num) hgap1 2
    calc
      _ ≤ 6 / 7 := hr1bound
      _ = 42 * (1 / 7 : ℝ) ^ 2 := by norm_num
      _ ≤ 42 * (1 - r1) ^ 2 :=
        mul_le_mul_of_nonneg_left hgapSq (by norm_num)
  have hbaseCoeff : baseCoeff ≤ 720 * gamma := by
    dsimp [baseCoeff]
    calc
      _ ≤ 540 * gamma * (4 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow12 (by positivity)
      _ = 720 * gamma := by ring
  have hbaseCoeff0 : 0 ≤ baseCoeff := by
    dsimp [baseCoeff]
    exact mul_nonneg (mul_nonneg (by norm_num) hgamma0)
      (Real.rpow_nonneg (by norm_num) _)
  have hnonlinearCoeff : nonlinearCoeff ≤ (201 / 125 : ℝ) * gamma := by
    dsimp [nonlinearCoeff]
    calc
      _ ≤ (603 / 500 : ℝ) * gamma * (4 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow48 (by positivity)
      _ = (201 / 125 : ℝ) * gamma := by ring
  have hnonlinearCoeff0 : 0 ≤ nonlinearCoeff := by
    dsimp [nonlinearCoeff]
    exact mul_nonneg (mul_nonneg (by norm_num) hgamma0)
      (Real.rpow_nonneg (by norm_num) _)
  have hpolyBound : a / (1 - r1) + b *
      (r1 / (1 - r1) ^ 2) ≤ 28504 := by
    have hfirst : a / (1 - r1) ≤ 28000 := by
      have hden : 0 < 1 - r1 := lt_of_lt_of_le (by norm_num) hgap1
      apply (div_le_iff₀ hden).2
      calc
        _ ≤ 4000 := ha
        _ = 28000 * (1 / 7 : ℝ) := by norm_num
        _ ≤ 28000 * (1 - r1) :=
          mul_le_mul_of_nonneg_left hgap1 (by norm_num)
    have hb0 : 0 ≤ b := mainRawS_nonneg hgamma0
    have hsecond : b * (r1 / (1 - r1) ^ 2) ≤ 504 := by
      have hratioNonneg : 0 ≤ r1 / (1 - r1) ^ 2 :=
        div_nonneg hr1nonneg (sq_nonneg (1 - r1))
      calc
        _ ≤ 12 * 42 := mul_le_mul hb hratioMoment hratioNonneg (by norm_num)
        _ = 504 := by norm_num
    calc
      _ ≤ 28000 + 504 := add_le_add hfirst hsecond
      _ = 28504 := by norm_num
  have hbaseBound : (1 - alpha) * (baseCoeff / (1 - r0)) ≤
      1260 * gamma := by
    have heq : (1 - alpha) * (baseCoeff / (1 - r0)) =
        ((1 - alpha) / (1 - r0)) * baseCoeff := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [heq]
    calc
      _ ≤ (7 / 4 : ℝ) * (720 * gamma) :=
        mul_le_mul hratio0 hbaseCoeff hbaseCoeff0 (by norm_num)
      _ = 1260 * gamma := by ring
  have hnonlinearBound : (1 - alpha) * (nonlinearCoeff *
      (a / (1 - r1) + b * (r1 / (1 - r1) ^ 2))) ≤ 11700 * gamma := by
    have hcoef : (1 - alpha) * nonlinearCoeff ≤
        (1 / 4 : ℝ) * ((201 / 125 : ℝ) * gamma) :=
      mul_le_mul hweight.2 hnonlinearCoeff hnonlinearCoeff0 (by norm_num)
    have ha0 : 0 ≤ a := mainRawA_nonneg hgamma0
    have hb0 : 0 ≤ b := mainRawS_nonneg hgamma0
    have hpolyNonneg : 0 ≤ a / (1 - r1) +
        b * (r1 / (1 - r1) ^ 2) := by
      have hr : 0 ≤ r1 / (1 - r1) ^ 2 :=
        div_nonneg hr1nonneg (sq_nonneg (1 - r1))
      exact add_nonneg (div_nonneg ha0 (by linarith [hgap1]))
        (mul_nonneg hb0 hr)
    calc
      _ = ((1 - alpha) * nonlinearCoeff) *
          (a / (1 - r1) + b * (r1 / (1 - r1) ^ 2)) := by ring
      _ ≤ ((1 / 4 : ℝ) * ((201 / 125 : ℝ) * gamma)) *
          (a / (1 - r1) + b * (r1 / (1 - r1) ^ 2)) :=
            mul_le_mul_of_nonneg_right hcoef hpolyNonneg
      _ ≤ ((1 / 4 : ℝ) * (201 / 125 : ℝ) * 28504) * gamma := by
            have hg0' : 0 ≤ gamma := hgamma0
            calc
              _ ≤ ((1 / 4 : ℝ) * ((201 / 125 : ℝ) * gamma)) * 28504 :=
                mul_le_mul_of_nonneg_left hpolyBound
                  (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hgamma0))
              _ = ((1 / 4 : ℝ) * (201 / 125 : ℝ) * 28504) * gamma := by ring
      _ ≤ 11700 * gamma := by
            apply mul_le_mul_of_nonneg_right _ hgamma0
            norm_num
  have hweightMajorant : (1 - alpha) *
      (∑' j : ℕ, beta ^ j *
        mainRawShellOldFrameP20Control M h m j) ≤ 13000 * gamma := by
    have hsumLE := hcontrolSummable.tsum_le_tsum hpointwise hmajorSummable
    calc
      _ ≤ (1 - alpha) * (∑' j : ℕ, majorant j) :=
        mul_le_mul_of_nonneg_left hsumLE hweight.1
      _ = (1 - alpha) *
          (baseCoeff / (1 - r0) + nonlinearCoeff *
            (a / (1 - r1) + b * (r1 / (1 - r1) ^ 2))) := by rw [hsumMajorant]
      _ ≤ 1260 * gamma + 11700 * gamma := by
        rw [mul_add]
        exact add_le_add hbaseBound hnonlinearBound
      _ ≤ 13000 * gamma := by nlinarith
  simpa only [gamma, beta, alpha] using ⟨hcontrolSummable, hweightMajorant⟩

private theorem main_max_history_population_weight (j : ℕ) :
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
private theorem main_rawDepth_lpNorm_twenty_bound_of_fixed_old_frame_control
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

private theorem main_max_history_base_ge_one : 1 ≤ mainH0 := by
  let r : ℝ := (3 : ℝ) ^ (3 / 4 : ℝ)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr4 : r ^ 4 = 27 := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hr : (4 / 3 : ℝ) ≤ r := by
    apply (pow_le_pow_iff_left₀ (by norm_num) hr0
      (by norm_num : (4 : ℕ) ≠ 0)).1
    rw [hr4]
    norm_num
  unfold mainH0
  calc
    _ ≤ (4 / 3 : ℝ) * (2379 / 2500 : ℝ) := by norm_num
    _ ≤ r * (2379 / 2500 : ℝ) :=
      mul_le_mul_of_nonneg_right hr (by norm_num)

private theorem main_envelopeH_max_history_cross_bound
    (M : ABKModel 2) (hgamma : M.gamma ≤ gammaZero)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    mainH0 + (553 / 125 : ℝ) * Real.sqrt (theta M * t) ≤
      mainEnvelopeH (theta M) M.gamma t := by
  have htheta0 : 0 ≤ theta M := (ASDExplicitGamma.Cold.cold_theta_pos M).le
  have htheta1 : theta M ≤ 1 := ASDExplicitGamma.Cold.cold_theta_le_one M hgamma
  let x : ℝ := theta M * t
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    calc
      _ ≤ 1 * t := mul_le_mul_of_nonneg_right htheta1 ht0
      _ = t := by ring
      _ ≤ 1 := ht1
  have hdelta0 : 0 ≤ mainDeltaH (theta M) M.gamma := by
    rw [mainDeltaH_eq_depth_tsum (theta M) M.gamma
      M.shellPrefix.gamma_pos.le hgamma]
    have hrows : ∀ j : ℕ, 0 ≤ mainEnvelopeHDepthGeneratorRow
        (theta M) M.gamma j := by
      intro j
      exact mainEnvelopeHDepthGeneratorRow_nonneg htheta0
        M.shellPrefix.gamma_pos.le hgamma j
    exact mul_nonneg
      (sub_nonneg.mpr (by
        dsimp [mainAlpha]
        exact Real.rpow_le_one_of_one_le_of_nonpos
          (by norm_num) (by norm_num)))
      (tsum_nonneg hrows)
  have hrad0 : 1 ≤ Real.sqrt
      (mainH0 + mainDeltaH (theta M) M.gamma * t) := by
    have hdt : 0 ≤ mainDeltaH (theta M) M.gamma * t := mul_nonneg hdelta0 ht0
    have hradarg0 : 0 ≤ mainH0 + mainDeltaH (theta M) M.gamma * t :=
      add_nonneg (le_trans (by norm_num) main_max_history_base_ge_one) hdt
    apply (Real.le_sqrt (by norm_num) hradarg0).2
    nlinarith [main_max_history_base_ge_one]
  let r : ℝ := (3 : ℝ) ^ (1 / 4 : ℝ)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr4 : r ^ 4 = 3 := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hr : (131 / 100 : ℝ) ≤ r := by
    apply (pow_le_pow_iff_left₀ (by norm_num) hr0
      (by norm_num : (4 : ℕ) ≠ 0)).1
    rw [hr4]
    norm_num
  have hbeta : 121 / 100 ≤ Real.sqrt mainBetaOld := by
    apply (Real.le_sqrt (by norm_num) (by norm_num [mainBetaOld])).2
    norm_num [mainBetaOld]
  have hfirst : (15851 / 10000 : ℝ) ≤ r * Real.sqrt mainBetaOld := by
    calc
      _ = (131 / 100 : ℝ) * (121 / 100 : ℝ) := by norm_num
      _ ≤ r * Real.sqrt mainBetaOld :=
        mul_le_mul hr hbeta (by norm_num) (by positivity)
  have hsource : (79 / 50 : ℝ) ≤
      r * Real.sqrt mainBetaOld +
        (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld := by
    have heps : 0 ≤ (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld := by
      positivity
    norm_num at hfirst ⊢
    linarith
  have hsqrt2 : (7 / 5 : ℝ) ≤ Real.sqrt 2 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hfactor : (553 / 250 : ℝ) ≤ Real.sqrt 2 *
      (r * Real.sqrt mainBetaOld +
        (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld) := by
    calc
      _ = (7 / 5 : ℝ) * (79 / 50 : ℝ) := by norm_num
      _ ≤ _ := mul_le_mul hsqrt2 hsource (by norm_num) (by positivity)
  let A : ℝ := Real.sqrt (mainH0 + mainDeltaH (theta M) M.gamma * t)
  let B : ℝ := Real.sqrt (2 * x) *
      (r * Real.sqrt mainBetaOld +
        (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld)
  have hAsq : A ^ 2 = mainH0 + mainDeltaH (theta M) M.gamma * t := by
    dsimp [A]
    rw [Real.sq_sqrt (add_nonneg
      (le_trans (by norm_num) main_max_history_base_ge_one)
      (mul_nonneg hdelta0 ht0))]
  have hAcross : (553 / 125 : ℝ) * Real.sqrt x ≤ 2 * A * B := by
    have hB0 : 0 ≤ B := by dsimp [B]; positivity
    have hBbound : (553 / 250 : ℝ) * Real.sqrt x ≤ B := by
      dsimp [B]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        _ ≤ (Real.sqrt 2 *
            (r * Real.sqrt mainBetaOld +
              (105 : ℝ) ^ (1 / 8 : ℝ) * Real.sqrt mainEpsOld)) *
              Real.sqrt x :=
          mul_le_mul_of_nonneg_right hfactor (Real.sqrt_nonneg x)
        _ = _ := by ring
    calc
      _ = 2 * ((553 / 250 : ℝ) * Real.sqrt x) := by ring
      _ ≤ 2 * B := mul_le_mul_of_nonneg_left hBbound (by norm_num)
      _ ≤ 2 * A * B := by
        have hA : 1 ≤ A := by simpa only [A] using hrad0
        nlinarith [hB0]
  have hdeltaT : 0 ≤ mainDeltaH (theta M) M.gamma * t :=
    mul_nonneg hdelta0 ht0
  calc
    _ ≤ A ^ 2 + 2 * A * B := by
      dsimp [A, x]
      rw [hAsq]
      nlinarith [hdeltaT, hAcross]
    _ ≤ (A + B) ^ 2 := by nlinarith [sq_nonneg B]
    _ = mainEnvelopeH (theta M) M.gamma t := by
      dsimp [A, B, r, mainEnvelopeH, x]
      rw [show Real.sqrt (2 * (theta M * t)) =
        Real.sqrt (2 * theta M * t) by congr 1 <;> ring]

private theorem main_ordinary_trace_max_history_eLpNorm_twenty_le_source
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eLpNorm (mainOrdinaryTraceMaxHistory M m
      (originCube 2 (m - 5)) t)
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (mainH0 + 13000 * M.gamma * t) := by
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
  have hB := main_ordinary_trace_max_old_profile_bound M m hgamma hstrong
  have hbeta : mainBetaPrime = coldHistoryBeta := by rfl
  have hBsum : Summable (fun j : ℕ => mainBetaPrime ^ j * B j) := by
    simpa only [B, hbeta] using hB.1
  have hBbound : (1 - mainAlpha) *
      ∑' j : ℕ, mainBetaPrime ^ j * B j ≤ mainH0 := by
    simpa only [B, hbeta] using hB.2
  have hC := main_rawShell_fixed_old_frame_p20_control_beta_discounted_bound
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
      mainH0 + 13000 * M.gamma * t := by
    have hAlphaLt : mainAlpha < 1 := by
      dsimp [mainAlpha]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    rw [hsplit]
    calc
      _ = (1 - mainAlpha) * (∑' j : ℕ, mainBetaPrime ^ j * B j) +
          t * ((1 - mainAlpha) *
            (∑' j : ℕ, mainBetaPrime ^ j * C j)) := by ring
      _ ≤ mainH0 + t * (13000 * M.gamma) :=
        add_le_add hBbound (mul_le_mul_of_nonneg_left hC.2 ht0)
      _ = _ := by ring
  have hFmeas (j : ℕ) : Measurable (F j) := by
    dsimp [F]
    exact (main_ordinary_trace_depth_max_measurable M m Q t j).const_mul _
  have hFbound (j : ℕ) :
      eLpNorm (F j) 20 μ ≤ ENNReal.ofReal (g j) := by
    have hraw := main_rawDepth_lpNorm_twenty_bound_of_fixed_old_frame_control
      M h hM hgamma m hpast hstrong t ht0 ht1 j
    have hdepth := main_ordinary_trace_depth_max_L20_bound
      M h hM hgamma m hpast t ht0 ht1 j
    have hscale : 0 ≤ mainAlpha ^ j := pow_nonneg
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) j
    have hbetaPow : 0 ≤ mainBetaPrime ^ j := pow_nonneg hBeta0 j
    have hpop := main_max_history_population_weight j
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
    _ ≤ ENNReal.ofReal (mainH0 + 13000 * M.gamma * t) :=
        ENNReal.ofReal_le_ofReal hweightBound

theorem main_ordinary_trace_max_history_memLp_two_le_mainEnvelopeH
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
      mainEnvelopeH (theta M) M.gamma t := by
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
  have hsource := main_ordinary_trace_max_history_eLpNorm_twenty_le_source
    M h hM hgamma m hpast t ht0 ht1
  have hEnvelope : mainH0 + 13000 * M.gamma * t ≤
      mainEnvelopeH (theta M) M.gamma t := by
    have htheta0 : 0 ≤ theta M := (ASDExplicitGamma.Cold.cold_theta_pos M).le
    let x := theta M * t
    have hx0 : 0 ≤ x := by dsimp [x]; positivity
    have hx1 : x ≤ 1 := by
      dsimp [x]
      calc
        _ ≤ 1 * t := mul_le_mul_of_nonneg_right
          (ASDExplicitGamma.Cold.cold_theta_le_one M hgamma) ht0
        _ = t := by ring
        _ ≤ 1 := ht1
    have hxsqrt : x ≤ Real.sqrt x := by
      apply (Real.le_sqrt hx0 hx0).2
      nlinarith [hx1]
    have hgammaTheta : 13000 * M.gamma = (221 / 50 : ℝ) * theta M := by
      rw [theta]
      field_simp [gammaZero]
      norm_num [gammaZero]
      ring
    have hclock : 13000 * M.gamma * t ≤
        (553 / 125 : ℝ) * Real.sqrt x := by
      calc
        _ = (221 / 50 : ℝ) * x := by rw [hgammaTheta]; dsimp [x]; ring
        _ ≤ (221 / 50 : ℝ) * Real.sqrt x :=
          mul_le_mul_of_nonneg_left hxsqrt (by norm_num)
        _ ≤ (553 / 125 : ℝ) * Real.sqrt x :=
          mul_le_mul_of_nonneg_right (by norm_num) (Real.sqrt_nonneg x)
    calc
      _ ≤ mainH0 + (553 / 125 : ℝ) * Real.sqrt x := add_le_add le_rfl hclock
      _ = mainH0 + (553 / 125 : ℝ) * Real.sqrt (theta M * t) := by rfl
      _ ≤ _ := main_envelopeH_max_history_cross_bound M hgamma t ht0 ht1
  have hEnvelope0 : 0 ≤ mainEnvelopeH (theta M) M.gamma t := by
    dsimp [mainEnvelopeH]
    positivity
  have hH20 : eLpNorm H 20 μ ≤
      ENNReal.ofReal (mainEnvelopeH (theta M) M.gamma t) := by
    calc
      _ ≤ ENNReal.ofReal (mainH0 + 13000 * M.gamma * t) := hsource
      _ ≤ _ := ENNReal.ofReal_le_ofReal hEnvelope
  have hH2 : eLpNorm H 2 μ ≤
      ENNReal.ofReal (mainEnvelopeH (theta M) M.gamma t) := by
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
  have hTbound : lpNorm T 2 μ ≤ mainEnvelopeH (theta M) M.gamma t := by
    change (eLpNorm T 2 μ).toReal ≤ mainEnvelopeH (theta M) M.gamma t
    rw [hTnorm]
    calc
      _ ≤ (ENNReal.ofReal (mainEnvelopeH (theta M) M.gamma t)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hH2
      _ = mainEnvelopeH (theta M) M.gamma t := ENNReal.toReal_ofReal hEnvelope0
  refine ⟨hfinite, ?_, ?_⟩
  · simpa only [T, H] using hTmem
  · simpa only [T, H] using hTbound

end

end ASDExplicitGamma.Main
