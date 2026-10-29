module

public import ASDExplicitGamma.Native.ReturnsFrame
public import ASDExplicitGamma.Native.HeatStepNodeClosed
public import ASDExplicitGamma.Native.GenericSourceDepthRows
public import ASDExplicitGamma.Native.HeatOldRawSound

/-! NA-RETURNS: the individual terms of the native histories. For the term of lag `g - 9`
(cube `N-(g-9)`, cutoff `N`), the source label is `K = N-g`; the true-frame `L^20` norm is bounded
by the sharp frame map applied to the old-frame cap, which is the refined heat step for
`9 ≤ g ≤ 160` and the raw OLD envelope for `161 ≤ g ≤ 1334`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native ASDExplicitGamma.Variational
open scoped ENNReal

/-- `3^x ≤ E(x)` on the rational frame domain. -/
theorem nativeReturns_three_pow_le_E (x : ℝ) (hx0 : 0 ≤ x) (hx1 : (11 / 10 : ℝ) * x < 1) :
    (3 : ℝ) ^ x ≤ (1 - (11 / 10 : ℝ) * x)⁻¹ := by
  have hlog : Real.log 3 ≤ 11 / 10 := by
    have := Real.log_three_lt_d9
    norm_num at this ⊢
    linarith
  have hx : x * Real.log 3 ≤ (11 / 10 : ℝ) * x := by nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)]
  have hexp : (3 : ℝ) ^ x = Real.exp (x * Real.log 3) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  rw [hexp]
  have hle : Real.exp (x * Real.log 3) ≤ Real.exp ((11 / 10 : ℝ) * x) := Real.exp_le_exp.mpr hx
  have hden : 0 < 1 - (11 / 10 : ℝ) * x := by linarith
  have hkey : Real.exp ((11 / 10 : ℝ) * x) * (1 - (11 / 10 : ℝ) * x) ≤ 1 := by
    have h := Real.one_sub_le_exp_neg ((11 / 10 : ℝ) * x)
    have hpos := Real.exp_pos ((11 / 10 : ℝ) * x)
    have : Real.exp ((11 / 10 : ℝ) * x) * (1 - (11 / 10 : ℝ) * x) ≤
        Real.exp ((11 / 10 : ℝ) * x) * Real.exp (-((11 / 10 : ℝ) * x)) :=
      mul_le_mul_of_nonneg_left h hpos.le
    rw [← Real.exp_add] at this
    simpa using this
  refine hle.trans ?_
  rw [← one_div, le_div_iff₀ hden]
  exact hkey

theorem nativeReturns_rawIncrement_mono (g : ℕ) {e e' f f' : ℝ} (he : e ≤ e') (hf : f ≤ f')
    (he0 : 0 ≤ e) (hf0 : 0 ≤ f) :
    nativeSourceRawMomentIncrement g e f ≤ nativeSourceRawMomentIncrement g e' f' := by
  unfold nativeSourceRawMomentIncrement nativeSourceK nativeSourceM nativeSourceQ nativeSourceB128
  have hX : ((78 * (g : ℝ) + 76 * (521 / 1000)) * (3683 / 2500) +
      2 * (521 / 1000) * (3683 / 2500) * f + (1975 / 1000 + 38 * (1565 / 1000)) * (3683 / 2500) ^ 2 * f) ≤
      ((78 * (g : ℝ) + 76 * (521 / 1000)) * (3683 / 2500) +
      2 * (521 / 1000) * (3683 / 2500) * f' + (1975 / 1000 + 38 * (1565 / 1000)) * (3683 / 2500) ^ 2 * f') := by
    nlinarith
  have hX0 : 0 ≤ ((78 * (g : ℝ) + 76 * (521 / 1000)) * (3683 / 2500) +
      2 * (521 / 1000) * (3683 / 2500) * f + (1975 / 1000 + 38 * (1565 / 1000)) * (3683 / 2500) ^ 2 * f) := by
    positivity
  exact mul_le_mul he hX hX0 (he0.trans he)

/-- The exponential raw frame input is below the rational OLD raw envelope at the endpoint. -/
theorem nativeReturns_rawInput_le (M : ABKModel 2) (hz : M.gamma = gammaZero) (g : ℕ)
    (hg : g ≤ 1334) :
    nativeSourceExponentialRawFrameInput M.gamma (theta M) g ≤
      ((nativeAvg * nativeA + (nativeRaw g).2.2 : ℚ) : ℝ) := by
  have hθ : theta M = 1 := by
    unfold theta; rw [hz]; exact div_self (by norm_num [gammaZero])
  have hγ : M.gamma = 17 / 50000 := by rw [hz]; rfl
  have hgR : (g : ℝ) ≤ 1334 := by exact_mod_cast hg
  have hinc := heat_old_raw_increment_le g
  have hvar : nativeSourceExponentialVarianceCap M.gamma g ≤ (((nativeRaw g).2.1 : ℚ) : ℝ) := by
    have hE := nativeReturns_three_pow_le_E (2 * (g : ℝ) * M.gamma) (by positivity)
      (by rw [hγ]; nlinarith)
    simp only [nativeRaw, nativeE, nativeGamma]
    unfold nativeSourceExponentialVarianceCap
    push_cast
    rw [hγ] at hE ⊢
    have h0 : (0 : ℝ) ≤ 9 / 2 * (17 / 50000 : ℝ) := by norm_num
    calc (9 / 2 : ℝ) * (17 / 50000) * (3 : ℝ) ^ (2 * (g : ℝ) * (17 / 50000)) ≤
        (9 / 2 : ℝ) * (17 / 50000) * (1 - (11 / 10 : ℝ) * (2 * (g : ℝ) * (17 / 50000)))⁻¹ :=
          mul_le_mul_of_nonneg_left hE h0
      _ = _ := by
        field_simp
  have hfull : nativeSourceExponentialFullResponseCap M.gamma g ≤ (((nativeRaw g).1 : ℚ) : ℝ) := by
    have hx0 : (0 : ℝ) ≤ (2 * (g : ℝ) + 4) * M.gamma := by positivity
    have hE := nativeReturns_three_pow_le_E ((2 * (g : ℝ) + 4) * M.gamma) hx0
      (by rw [hγ]; nlinarith)
    have hup := nativeUp_ge (4 * ((1009309 / 500000) + nativeGamma * (32474 * ((g : ℚ) + 1) + 11483216)) *
      nativeE ((2 * (g : ℚ) + 4) * nativeGamma))
    have hupR := (Rat.cast_le (K := ℝ)).2 hup
    refine le_trans ?_ hupR
    unfold nativeSourceExponentialFullResponseCap
    simp only [nativeE, nativeGamma]
    push_cast
    rw [hγ] at hE ⊢
    have h0 : (0 : ℝ) ≤ 4 * (1009309 / 500000 + 17 / 50000 * (32474 * ((g : ℝ) + 1) + 11483216)) := by
      positivity
    calc _ ≤ 4 * (1009309 / 500000 + 17 / 50000 * (32474 * ((g : ℝ) + 1) + 11483216)) *
        (1 - (11 / 10 : ℝ) * ((2 * (g : ℝ) + 4) * (17 / 50000)))⁻¹ := by
          have := mul_le_mul_of_nonneg_left hE h0
          simpa [Nat.cast_add, Nat.cast_one] using this
      _ = _ := by
        field_simp
  have hmono := nativeReturns_rawIncrement_mono g hvar hfull
    (by unfold nativeSourceExponentialVarianceCap; positivity)
    (by unfold nativeSourceExponentialFullResponseCap; positivity)
  have hincr : nativeSourceExponentialRawIncrement M.gamma g ≤ (((nativeRaw g).2.2 : ℚ) : ℝ) :=
    hmono.trans hinc
  unfold nativeSourceExponentialRawFrameInput
  rw [hθ]
  push_cast
  have : nativeSourceAverageFactor = (nativeAvg : ℝ) := by
    norm_num [nativeSourceAverageFactor, nativeAvg, nativeRoot]
  have hA : (nativeA : ℝ) = 3 / 50 := by norm_num [nativeA]
  rw [this, hA]
  linarith

/-- The rational OLD raw envelope is nonnegative on the frame domain. -/
theorem nativeReturns_raw_entry_nonneg (M : ABKModel 2) (hz : M.gamma = gammaZero) (g : ℕ)
    (hg : g ≤ 1334) :
    (0 : ℝ) ≤ ((nativeAvg * nativeA + (nativeRaw g).2.2 : ℚ) : ℝ) := by
  refine le_trans ?_ (nativeReturns_rawInput_le M hz g hg)
  have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have ht0 : 0 ≤ theta M := div_nonneg hγ (by norm_num [gammaZero])
  dsimp only [nativeSourceExponentialRawFrameInput, nativeSourceExponentialRawIncrement,
    nativeSourceExponentialVarianceCap, nativeSourceExponentialFullResponseCap,
    nativeSourceAverageFactor, nativeSourceRawMomentIncrement, nativeSourceK, nativeSourceM,
    nativeSourceQ, nativeSourceB128]
  positivity

/-- Heat terms `9 ≤ g ≤ 160`, with the carrier index `m` (label `m+1`, cube `m+10`, cutoff `m+1+g`). -/
theorem nativeReturns_term_heat_m (g : ℕ) [NeZero g] (hg9 : 9 ≤ g) (hg160 : g ≤ 160)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hgam : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m + 1, nativeInductionState M h j)
    (hstate : nativeInductionState M h (m + 1))
    (hq0 : 0 ≤ (nativeHeatResultGen g).1) :
    eLpNorm (cutoffTraceDefect M (m + 1 + (g : ℤ)) (m + 10)) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (nativeFrameReal (((11 / 10) * (2 * nativeGamma * (g : ℚ)) : ℚ) : ℝ)
        (((nativeHeatResultGen g).1 : ℚ) : ℝ)) := by
  have hheat := (nativeRefinedHeatStep_Gen_closed g hg9 hg160 M h hM hgam m hpast hstate).1
  exact nativeReturns_cutoffTrace_frame M hgam (m + 1) g (by omega) (m + 10)
    ((nativeHeatResultGen g).1) (by exact_mod_cast hq0) hheat

/-- Heat terms at the frozen indices: cube `N-(g-9)`, cutoff `N`, from the states below `N`. -/
theorem nativeReturns_term_heat (g : ℕ) (hg9 : 9 ≤ g) (hg160 : g ≤ 160)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hgam : M.gamma ≤ gammaZero) (N : ℤ)
    (hN : ∀ n < N, nativeInductionState M h n)
    (hq0 : 0 ≤ (nativeHeatResultGen g).1) :
    eLpNorm (cutoffTraceDefect M N (N - ((g - 9 : ℕ) : ℤ))) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (nativeFrameReal (((11 / 10) * (2 * nativeGamma * (g : ℚ)) : ℚ) : ℝ)
        (((nativeHeatResultGen g).1 : ℚ) : ℝ)) := by
  haveI : NeZero g := ⟨by omega⟩
  have key := nativeReturns_term_heat_m g hg9 hg160 M h hM hgam (N - (g : ℤ) - 1)
    (fun j hj => hN j (by omega)) (hN _ (by omega)) hq0
  have e1 : N - (g : ℤ) - 1 + 1 + (g : ℤ) = N := by ring
  have e2 : N - (g : ℤ) - 1 + 10 = N - ((g - 9 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hg9]; push_cast; ring
  rw [e1, e2] at key
  exact key

/-- Raw terms `g ≤ 1334` at the endpoint: the exponential raw OLD envelope on the child, the sharp
frame map, and the coarse subadditivity to the parent cube. -/
theorem nativeReturns_term_raw (g : ℕ) (hg9 : 9 ≤ g) (hg1334 : g ≤ 1334)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hz : M.gamma = gammaZero) (N : ℤ)
    (hN : ∀ n < N, nativeInductionState M h n) :
    eLpNorm (cutoffTraceDefect M N (N - ((g - 9 : ℕ) : ℤ))) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (nativeFrameReal (((11 / 10) * (2 * nativeGamma * (g : ℚ)) : ℚ) : ℝ)
        (((nativeAvg * nativeA + (nativeRaw g).2.2 : ℚ) : ℝ))) := by
  have hgam : M.gamma ≤ gammaZero := hz.le
  set K : ℤ := N - (g : ℤ) with hK
  have hpast : ∀ j < K, nativeInductionState M h j := fun j hj => hN j (by omega)
  have hstate : nativeInductionState M h K := hN K (by omega)
  have hraw := native_source_band_trace_raw_allowance M h hM hgam K hpast hstate g hg9
  have hrawle := nativeReturns_rawInput_le M hz g hg1334
  have hq0 := nativeReturns_raw_entry_nonneg M hz g hg1334
  -- the child trace, in the old frame, as an extended `L^20` norm
  have hfun : (fun ω : Cutoff.CutoffSample 2 => modelTraceObservable K M.nu (Annealed.sigmaBar M K)
      (nativeSourceBandScalar K g 1 ω)) = fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet (originCube 2 K))
        (Cutoff.coefficientCutoff M.nu (K + (g : ℤ)) ω).toFun (Annealed.sigmaBar M K : ℝ) := by
    funext ω
    exact native_source_band_trace_one M K g ω
  rw [hfun] at hraw
  have hTm := nativeReturns_traceDefect_measurable M (K + (g : ℤ)) K (Annealed.sigmaBar M K : ℝ)
  have hchild : eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet (originCube 2 K))
        (Cutoff.coefficientCutoff M.nu (K + (g : ℤ)) ω).toFun (Annealed.sigmaBar M K : ℝ))
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (((nativeAvg * nativeA + (nativeRaw g).2.2 : ℚ) : ℝ)) := by
    rw [eLpNorm_eq_eLpNorm' (by norm_num : (20 : ℝ≥0∞) ≠ 0) (by norm_num : (20 : ℝ≥0∞) ≠ ⊤)
      hTm.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    exact hraw.trans (ENNReal.ofReal_le_ofReal hrawle)
  have hfr := nativeReturns_cutoffTrace_frame M hgam K g hg1334 K _ hq0 hchild
  have hA : 0 ≤ nativeFrameReal (((11 / 10) * (2 * nativeGamma * (g : ℚ)) : ℚ) : ℝ)
      (((nativeAvg * nativeA + (nativeRaw g).2.2 : ℚ) : ℝ)) := by
    refine nativeFrameReal_nonneg _ _ (by push_cast; norm_num [nativeGamma]) ?_ hq0
    push_cast
    have hgR : (g : ℝ) ≤ 1334 := by exact_mod_cast hg1334
    norm_num [nativeGamma]
    nlinarith
  have hTn := cutoffTraceDefect_measurable M (K + (g : ℤ)) K
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (20 : ℝ≥0∞) ≠ 0) (by norm_num : (20 : ℝ≥0∞) ≠ ⊤)
    hTn.aestronglyMeasurable] at hfr
  simp only [ENNReal.toReal_ofNat] at hfr
  have hscale : (originCube 2 (K + 9)).scale - ((9 : ℕ) : ℤ) = K := by
    simp [originCube]
  have hpar := native_source_parent_L20_cap M (K + (g : ℤ)) (originCube 2 (K + 9)) 9 _ hA
    (by rw [hscale]; exact hfr)
  have hpar' : eLpNorm (cutoffTraceDefect M (K + (g : ℤ)) (originCube 2 (K + 9)).scale) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (nativeFrameReal
        (((11 / 10) * (2 * nativeGamma * (g : ℚ)) : ℚ) : ℝ)
        (((nativeAvg * nativeA + (nativeRaw g).2.2 : ℚ) : ℝ))) := by
    rw [eLpNorm_eq_eLpNorm' (by norm_num : (20 : ℝ≥0∞) ≠ 0) (by norm_num : (20 : ℝ≥0∞) ≠ ⊤)
      (cutoffTraceDefect_measurable M (K + (g : ℤ)) (originCube 2 (K + 9)).scale).aestronglyMeasurable]
    simpa only [ENNReal.toReal_ofNat] using hpar
  have e1 : K + (g : ℤ) = N := by rw [hK]; ring
  have e2 : (originCube 2 (K + 9)).scale = N - ((g - 9 : ℕ) : ℤ) := by
    simp only [originCube]
    rw [hK, Nat.cast_sub hg9]; push_cast; ring
  rw [e1, e2] at hpar'
  exact hpar'

end ASDExplicitGamma.Native
