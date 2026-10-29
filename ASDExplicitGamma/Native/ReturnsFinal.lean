module

public import ASDExplicitGamma.Native.ReturnsHistory
public import ASDExplicitGamma.Native.ReturnsMean
public import ASDExplicitGamma.Statements.Root20

/-! NA-RETURNS: the four native returns at the endpoint. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Native ASDExplicitGamma.Variational
open scoped ENNReal

/-- The closed raw tail of a history with weights `Q_H^r`. -/
theorem nativeReturns_tail_bound (M : ABKModel 2) (hz : M.gamma = gammaZero) (offset : ℕ)
    (hoff1 : 1 ≤ offset) (hoff : offset ≤ 49) (U : ℕ → ℝ≥0∞)
    (htail : ∀ r, 1286 ≤ r → U r ≤
      ENNReal.ofReal (nativeSourceExponentialRawFrame M.gamma (theta M) (offset + r))) :
    ENNReal.ofReal (nativeC0 : ℝ) * ∑' j : ℕ,
        ENNReal.ofReal ((nativeHistoryRatio : ℝ) ^ (j + 1286)) * U (j + 1286) ≤
      ENNReal.ofReal ((nativeSourceHistoryTail offset : ℚ) : ℝ) := by
  have hγ : M.gamma = 17 / 50000 := by rw [hz]; rfl
  have hγ0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hθ0 : 0 ≤ theta M := div_nonneg hγ0 (by norm_num [gammaZero])
  set q : ℝ := (nativeHistoryRatio : ℝ) with hq
  set growth : ℝ := (3 : ℝ) ^ (6 * M.gamma) with hgrowth
  set raw : ℕ → ℝ := nativeSourceExponentialRawFrame M.gamma (theta M) with hraw
  have hq0 : 0 ≤ q := by rw [hq]; norm_num [nativeHistoryRatio]
  have hgrowth0 : 0 ≤ growth := by positivity
  have hratio : q * growth ≤ 9 / 10 := by
    have hE := nativeReturns_three_pow_le_E (6 * M.gamma) (by positivity) (by rw [hγ]; norm_num)
    have hE' : growth ≤ (1 - (11 / 10 : ℝ) * (6 * M.gamma))⁻¹ := hE
    rw [hγ] at hE'
    have h1 : q * growth ≤ q * (1 - (11 / 10 : ℝ) * (6 * (17 / 50000)))⁻¹ :=
      mul_le_mul_of_nonneg_left hE' hq0
    refine h1.trans ?_
    rw [hq]; norm_num [nativeHistoryRatio]
  have hraw0 : ∀ j, 0 ≤ raw j := fun j => native_source_actual_exponential_raw_frame_nonneg M j
  have hframe : ∀ j, raw (offset + j) ≤ raw offset * ((j + 1 : ℕ) : ℝ) ^ 2 * growth ^ j := by
    intro j
    simpa [hgrowth, hraw, mul_assoc] using
      native_source_exponential_raw_frame_growth M.gamma (theta M) offset j hγ0 hθ0 hoff1
  have hs : Summable (fun j : ℕ => q ^ j * raw (offset + j)) := by
    have hmajor := native_source_geom_quadratic_summable.mul_left (raw offset)
    apply Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hq0 j) (hraw0 _)) _ hmajor
    intro j
    have hpow := pow_le_pow_left₀ (mul_nonneg hq0 hgrowth0) hratio j
    calc
      _ ≤ q ^ j * (raw offset * ((j + 1 : ℕ) : ℝ) ^ 2 * growth ^ j) :=
        mul_le_mul_of_nonneg_left (hframe j) (pow_nonneg hq0 j)
      _ = raw offset * (((j : ℝ) + 1) ^ 2 * (q * growth) ^ j) := by push_cast; rw [mul_pow]; ring
      _ ≤ raw offset * (((j : ℝ) + 1) ^ 2 * (9 / 10 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (sq_nonneg _)) (hraw0 offset)
  have hshift : Summable (fun j : ℕ => q ^ (j + 1286) * raw (offset + (j + 1286))) :=
    (summable_nat_add_iff 1286).mpr hs
  have hnn : ∀ j : ℕ, 0 ≤ q ^ (j + 1286) * raw (offset + (j + 1286)) :=
    fun j => mul_nonneg (pow_nonneg hq0 _) (hraw0 _)
  have hmaj := native_source_raw_weighted_tail_le q growth offset 1285 raw hq0 hgrowth0 hratio
    (hraw0 offset) (fun j => hraw0 _) hframe
  have htailEq : nativeSourceRawWeightedTail q offset 1285 raw =
      ∑' j : ℕ, q ^ (j + 1286) * raw (offset + (j + 1286)) := by
    unfold nativeSourceRawWeightedTail
    apply tsum_congr
    intro j
    rw [show 1285 + 1 + j = j + 1286 by omega]
  rw [htailEq] at hmaj
  have hstep : ∑' j : ℕ, ENNReal.ofReal (q ^ (j + 1286)) * U (j + 1286) ≤
      ENNReal.ofReal (∑' j : ℕ, q ^ (j + 1286) * raw (offset + (j + 1286))) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hshift]
    apply ENNReal.tsum_le_tsum
    intro j
    rw [ENNReal.ofReal_mul (pow_nonneg hq0 _)]
    exact mul_le_mul' le_rfl (htail (j + 1286) (by omega))
  have hC0 : (0 : ℝ) ≤ nativeC0 := by norm_num [nativeC0]
  have hraw_le := nativeReturns_rawExp_le_rat M hz offset (by omega)
  calc ENNReal.ofReal (nativeC0 : ℝ) * ∑' j : ℕ, ENNReal.ofReal (q ^ (j + 1286)) * U (j + 1286)
      ≤ ENNReal.ofReal (nativeC0 : ℝ) *
          ENNReal.ofReal (∑' j : ℕ, q ^ (j + 1286) * raw (offset + (j + 1286))) :=
        mul_le_mul' le_rfl hstep
    _ = ENNReal.ofReal ((nativeC0 : ℝ) *
          ∑' j : ℕ, q ^ (j + 1286) * raw (offset + (j + 1286))) := (ENNReal.ofReal_mul hC0).symm
    _ ≤ ENNReal.ofReal ((nativeSourceHistoryTail offset : ℚ) : ℝ) := by
        apply ENNReal.ofReal_le_ofReal
        unfold nativeSourceHistoryTail
        push_cast
        have h1 : (nativeC0 : ℝ) * ∑' j : ℕ, q ^ (j + 1286) * raw (offset + (j + 1286)) ≤
            (nativeC0 : ℝ) * (raw offset * ((1285 + 2 : ℕ) : ℝ) ^ 4 * (9 / 10 : ℝ) ^ (1285 + 1) *
              (((Nat.factorial 4 : ℕ) : ℝ) * 10 ^ 5)) :=
          mul_le_mul_of_nonneg_left hmaj hC0
        refine h1.trans ?_
        have h2 : raw offset ≤ ((nativeSourceRawFrame offset : ℚ) : ℝ) := hraw_le
        have hc : (0 : ℝ) ≤ (nativeC0 : ℝ) * ((1285 + 2 : ℕ) : ℝ) ^ 4 * (9 / 10 : ℝ) ^ (1285 + 1) *
            (((Nat.factorial 4 : ℕ) : ℝ) * 10 ^ 5) := by positivity
        have := mul_le_mul_of_nonneg_left h2 hc
        push_cast at this ⊢
        nlinarith [this]

theorem nativeReturns_entry_nonneg (M : ABKModel 2) (hz : M.gamma = gammaZero) (g : ℕ)
    (hg9 : 9 ≤ g) (hg : g ≤ 1334) : 0 ≤ nativeReturnsEntry g := by
  unfold nativeReturnsEntry
  split_ifs with h160
  · have := nativeHeatResultGen_fst_nonneg g hg9 h160
    rwa [nativeHeatResultGen_eq_table g hg9 h160] at this
  · have := nativeReturns_raw_entry_nonneg M hz g hg
    exact_mod_cast this

/-- The term of total gap `g` is bounded through the certified entry. -/
theorem nativeReturns_term_entry (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hz : M.gamma = gammaZero) (N : ℤ) (hN : ∀ n < N, nativeInductionState M h n) (g : ℕ)
    (hg9 : 9 ≤ g) (hg : g ≤ 1334) :
    eLpNorm (cutoffTraceDefect M N (N - ((g - 9 : ℕ) : ℤ))) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (nativeFrameReal (((11 / 10) * (2 * nativeGamma * (g : ℚ)) : ℚ) : ℝ)
        ((nativeReturnsEntry g : ℚ) : ℝ)) := by
  unfold nativeReturnsEntry
  split_ifs with h160
  · have hq0 := nativeHeatResultGen_fst_nonneg g hg9 h160
    have := nativeReturns_term_heat g hg9 h160 M h hM hz.le N hN hq0
    rw [nativeHeatResultGen_eq_table g hg9 h160] at this
    exact this
  · exact nativeReturns_term_raw g hg9 hg M h hM hz N hN

theorem nativeReturns_xs_nonneg (M : ABKModel 2) (hz : M.gamma = gammaZero) (offset : ℕ)
    (hoff9 : 9 ≤ offset) (hoff : offset ≤ 49) (xs : List ℚ) (hlen : xs.length = 1286)
    (hentry : ∀ i < 1286, xs.getD i 0 = nativeReturnsEntry (offset + i)) :
    ∀ t ∈ xs, 0 ≤ t := by
  intro t ht
  obtain ⟨i, hi, hit⟩ := List.mem_iff_getElem.mp ht
  have hi' : i < 1286 := by omega
  have := hentry i hi'
  rw [List.getD_eq_getElem _ _ hi] at this
  rw [← hit, this]
  exact nativeReturns_entry_nonneg M hz (offset + i) (by omega) (by omega)

/-- The generic bound of a weighted history by the certified sum plus tail. -/
theorem nativeReturns_history_bound (M : ABKModel 2) (hz : M.gamma = gammaZero) (offset : ℕ)
    (hoff9 : 9 ≤ offset) (hoff : offset ≤ 49) (xs : List ℚ) (hlen : xs.length = 1286)
    (hentry : ∀ i < 1286, xs.getD i 0 = nativeReturnsEntry (offset + i))
    (U : ℕ → ℝ≥0∞)
    (hterm : ∀ i < 1286, U i ≤ ENNReal.ofReal (nativeFrameReal
      (((11 / 10) * (2 * nativeGamma * ((offset + i : ℕ) : ℚ)) : ℚ) : ℝ)
        ((nativeReturnsEntry (offset + i) : ℚ) : ℝ)))
    (htail : ∀ r, 1286 ≤ r → U r ≤
      ENNReal.ofReal (nativeSourceExponentialRawFrame M.gamma (theta M) (offset + r))) :
    ENNReal.ofReal (nativeC0 : ℝ) * ∑' r : ℕ, ENNReal.ofReal ((nativeHistoryRatio : ℝ) ^ r) * U r ≤
      ENNReal.ofReal (nativeHistoryReal offset 0 xs + ((nativeSourceHistoryTail offset : ℚ) : ℝ)) := by
  have hxs := nativeReturns_xs_nonneg M hz offset hoff9 hoff xs hlen hentry
  have hfin := nativeReturns_finite_sum U offset xs 0 hxs (by omega) (by
    intro i hi
    have hi' : i < 1286 := by omega
    have h1 := hterm i hi'
    rw [← hentry i hi'] at h1
    simpa using h1)
  have htl := nativeReturns_tail_bound M hz offset (by omega) hoff U htail
  have hEN : Summable (fun j : ℕ => ENNReal.ofReal ((nativeHistoryRatio : ℝ) ^ (j + 1286)) *
      U (j + 1286)) := ENNReal.summable
  have hsplit := hEN.sum_add_tsum_nat_add' (f := fun j : ℕ =>
    ENNReal.ofReal ((nativeHistoryRatio : ℝ) ^ j) * U j) (k := 1286)
  rw [← hsplit, mul_add]
  have h0 : 0 ≤ nativeHistoryReal offset 0 xs :=
    nativeReturns_historyReal_nonneg offset xs 0 hxs (by omega)
  have ht0 : (0 : ℝ) ≤ ((nativeSourceHistoryTail offset : ℚ) : ℝ) := by
    have hrf : (0 : ℝ) ≤ ((nativeSourceRawFrame offset : ℚ) : ℝ) :=
      (native_source_actual_exponential_raw_frame_nonneg M offset).trans
        (nativeReturns_rawExp_le_rat M hz offset (by omega))
    have hC : (0 : ℝ) ≤ nativeC0 := by norm_num [nativeC0]
    unfold nativeSourceHistoryTail
    push_cast
    have := mul_nonneg hC hrf
    positivity
  rw [ENNReal.ofReal_add h0 ht0]
  refine add_le_add ?_ htl
  rw [← hlen]
  simpa using hfin

theorem nativeReturns_strong20_le (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hz : M.gamma = gammaZero) (N : ℤ) (hN : ∀ n < N, nativeInductionState M h n) :
    strong20 M N ≤ ENNReal.ofReal nativeSourceStrongHistory := by
  set U : ℕ → ℝ≥0∞ := fun r => eLpNorm (cutoffTraceDefect M N (N - (r : ℤ))) 20
    (Cutoff.cutoffSampleLaw M).toMeasure with hU
  have h1 : strong20 M N ≤ ENNReal.ofReal (nativeC0 : ℝ) *
      ∑' r : ℕ, ENNReal.ofReal ((nativeHistoryRatio : ℝ) ^ r) * U r := by
    unfold strong20
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal nativeReturns_alpha_le)
      (ENNReal.tsum_le_tsum fun r => mul_le_mul' (ENNReal.ofReal_le_ofReal (nativeReturns_weight_le r))
        le_rfl)
  refine h1.trans ?_
  have hlen := nativeHistoryStrongCompletePrefix41_length
  have hentry : ∀ i < 1286, nativeHistoryStrongCompletePrefix41.getD i 0 =
      nativeReturnsEntry (9 + i) := nativeReturns_strong_prefix_41
  have := nativeReturns_history_bound M hz 9 le_rfl (by norm_num)
    nativeHistoryStrongCompletePrefix41 hlen hentry U
    (by
      intro i hi
      have h2 := nativeReturns_term_entry M h hM hz N hN (9 + i) (by omega) (by omega)
      rw [show 9 + i - 9 = i by omega] at h2
      exact h2)
    (by
      intro r hr
      have h3 := native_source_depth_exponential_eLpNorm M h hM hz.le N (fun k hk => hN k hk) r
      exact h3)
  exact this

theorem nativeReturns_buffer40History_le (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hz : M.gamma = gammaZero) (N : ℤ) (hN : ∀ n < N, nativeInductionState M h n) :
    buffer40History M N ≤ ENNReal.ofReal nativeSourceBufferHistory := by
  set U : ℕ → ℝ≥0∞ := fun r => eLpNorm (cutoffTraceDefect M N (N - 40 - (r : ℤ))) 20
    (Cutoff.cutoffSampleLaw M).toMeasure with hU
  have h1 : buffer40History M N ≤ ENNReal.ofReal (nativeC0 : ℝ) *
      ∑' r : ℕ, ENNReal.ofReal ((nativeHistoryRatio : ℝ) ^ r) * U r := by
    unfold buffer40History
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal nativeReturns_alpha_le)
      (ENNReal.tsum_le_tsum fun r => mul_le_mul' (ENNReal.ofReal_le_ofReal (nativeReturns_weight_le r))
        le_rfl)
  refine h1.trans ?_
  have hlen := nativeHistoryBufferCompletePrefix41_length
  have hentry : ∀ i < 1286, nativeHistoryBufferCompletePrefix41.getD i 0 =
      nativeReturnsEntry (49 + i) := nativeReturns_buffer_prefix_41
  have := nativeReturns_history_bound M hz 49 (by norm_num) le_rfl
    nativeHistoryBufferCompletePrefix41 hlen hentry U
    (by
      intro i hi
      have h2 := nativeReturns_term_entry M h hM hz N hN (49 + i) (by omega) (by omega)
      have e1 : N - (((49 + i - 9 : ℕ)) : ℤ) = N - 40 - (i : ℤ) := by
        rw [show 49 + i - 9 = 40 + i by omega]; push_cast; ring
      rw [e1] at h2
      exact h2)
    (by
      intro r hr
      have h3 := native_source_depth_exponential_eLpNorm M h hM hz.le N (fun k hk => hN k hk) (40 + r)
      have e1 : N - ((40 + r : ℕ) : ℤ) = N - 40 - (r : ℤ) := by push_cast; ring
      rw [e1, show 9 + (40 + r) = 49 + r by omega] at h3
      exact h3)
  exact this

theorem nativeReturns_root20_le (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgam : M.gamma ≤ gammaZero) (N : ℤ) (hN : ∀ n < N, nativeInductionState M h n) :
    root20 M N ≤ ENNReal.ofReal (nativeFrameReal
      (((11 / 10) * (2 * nativeGamma * (9 : ℕ)) : ℚ) : ℝ) (nativeHeat009Result.1 : ℝ)) := by
  have hq0 : 0 ≤ (nativeHeatResultGen 9).1 := nativeHeatResultGen_fst_nonneg 9 le_rfl (by norm_num)
  have := nativeReturns_term_heat 9 le_rfl (by norm_num) M h hM hgam N hN hq0
  rw [nativeHeatResultGen_009] at this
  simpa [root20] using this

/-- NA-RETURNS at the endpoint `γ = γ₀`: the four native returns below the displayed strict
returns, and below the frozen carried caps. -/
theorem nativeReturns_node (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hz : M.gamma = gammaZero) (N : ℤ) (hN : ∀ n < N, nativeInductionState M h n) :
    strong20 M N < ENNReal.ofReal (9515063 / 10 ^ 7) ∧
    ENNReal.ofReal (9515063 / 10 ^ 7) < ENNReal.ofReal (95151 / 100000) ∧
    strong20 M N < ENNReal.ofReal (2379 / 2500) ∧
    root20 M N < ENNReal.ofReal (2012545 / 10 ^ 7) ∧
    root20 M N < ENNReal.ofReal (2013 / 10000) ∧
    buffer40History M N < ENNReal.ofReal (5856633 / 10 ^ 6) ∧
    buffer40History M N < ENNReal.ofReal (61 / 10) ∧
    bufferMean M N < ENNReal.ofReal (317279 / 10 ^ 6) ∧
    bufferMean M N < ENNReal.ofReal (8 / 25) := by
  have hs := nativeReturns_strong20_le M h hM hz N hN
  have hb := nativeReturns_buffer40History_le M h hM hz N hN
  have hr := nativeReturns_root20_le M h hM hz.le N hN
  have hm := nativeReturns_bufferMean M h hM hz.le N hN
  obtain ⟨n1, n2, n3, n4⟩ := native_all_sharp_return_values
  obtain ⟨c1, c2, c3, c4⟩ := native_all_return_caps
  have lt : ∀ {x : ℝ≥0∞} {a b : ℝ}, 0 < b → x ≤ ENNReal.ofReal a → a < b →
      x < ENNReal.ofReal b := fun hb hx hab =>
    lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff hb).2 hab)
  refine ⟨lt (by norm_num) hs n1,
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num),
    lt (by norm_num) hs c1, lt (by norm_num) hr n2, lt (by norm_num) hr c2,
    lt (by norm_num) hb n3, lt (by norm_num) hb c3, lt (by norm_num) hm n4,
    lt (by norm_num) hm c4⟩

end ASDExplicitGamma.Native
