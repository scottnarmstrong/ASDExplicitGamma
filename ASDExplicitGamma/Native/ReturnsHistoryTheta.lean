module

public import ASDExplicitGamma.Native.ReturnsTermsTheta2
public import ASDExplicitGamma.Native.ReturnsFinal

/-! NA-RETURNS at smaller gamma: the theta-scaled weighted history bound (finite certified prefix
plus closed raw tail). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Native ASDExplicitGamma.Variational
open scoped ENNReal

/-- The closed raw tail of a history with weights `Q_H^r`. -/
theorem nativeReturns_tail_bound_theta (M : ABKModel 2) (hz : M.gamma ≤ gammaZero) (offset : ℕ)
    (hoff1 : 1 ≤ offset) (hoff : offset ≤ 49) (U : ℕ → ℝ≥0∞)
    (htail : ∀ r, 1286 ≤ r → U r ≤
      ENNReal.ofReal (nativeSourceExponentialRawFrame M.gamma (theta M) (offset + r))) :
    ENNReal.ofReal (nativeC0 : ℝ) * ∑' j : ℕ,
        ENNReal.ofReal ((nativeHistoryRatio : ℝ) ^ (j + 1286)) * U (j + 1286) ≤
      ENNReal.ofReal (theta M * ((nativeSourceHistoryTail offset : ℚ) : ℝ)) := by
  have hγ : M.gamma ≤ 17 / 50000 := by simpa [gammaZero] using hz
  have hγ0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hθ0 : 0 ≤ theta M := div_nonneg hγ0 (by norm_num [gammaZero])
  set q : ℝ := (nativeHistoryRatio : ℝ) with hq
  set growth : ℝ := (3 : ℝ) ^ (6 * M.gamma) with hgrowth
  set raw : ℕ → ℝ := nativeSourceExponentialRawFrame M.gamma (theta M) with hraw
  have hq0 : 0 ≤ q := by rw [hq]; norm_num [nativeHistoryRatio]
  have hgrowth0 : 0 ≤ growth := by positivity
  have hratio : q * growth ≤ 9 / 10 := by
    have hE := nativeReturns_three_pow_le_E (6 * M.gamma) (by positivity) (by nlinarith)
    have hE' : growth ≤ (1 - (11 / 10 : ℝ) * (6 * M.gamma))⁻¹ := hE
    have hE'' : (1 - (11 / 10 : ℝ) * (6 * M.gamma))⁻¹ ≤ (1 - (11 / 10 : ℝ) * (6 * (17 / 50000)))⁻¹ := by
      apply inv_anti₀ (by norm_num) (by nlinarith)
    have h1 : q * growth ≤ q * (1 - (11 / 10 : ℝ) * (6 * (17 / 50000)))⁻¹ :=
      mul_le_mul_of_nonneg_left (hE'.trans hE'') hq0
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
  have hraw_le := nativeReturns_rawExp_theta_le_rat M hz offset (by omega)
  calc ENNReal.ofReal (nativeC0 : ℝ) * ∑' j : ℕ, ENNReal.ofReal (q ^ (j + 1286)) * U (j + 1286)
      ≤ ENNReal.ofReal (nativeC0 : ℝ) *
          ENNReal.ofReal (∑' j : ℕ, q ^ (j + 1286) * raw (offset + (j + 1286))) :=
        mul_le_mul' le_rfl hstep
    _ = ENNReal.ofReal ((nativeC0 : ℝ) *
          ∑' j : ℕ, q ^ (j + 1286) * raw (offset + (j + 1286))) := (ENNReal.ofReal_mul hC0).symm
    _ ≤ ENNReal.ofReal (theta M * ((nativeSourceHistoryTail offset : ℚ) : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        unfold nativeSourceHistoryTail
        push_cast
        have h1 : (nativeC0 : ℝ) * ∑' j : ℕ, q ^ (j + 1286) * raw (offset + (j + 1286)) ≤
            (nativeC0 : ℝ) * (raw offset * ((1285 + 2 : ℕ) : ℝ) ^ 4 * (9 / 10 : ℝ) ^ (1285 + 1) *
              (((Nat.factorial 4 : ℕ) : ℝ) * 10 ^ 5)) :=
          mul_le_mul_of_nonneg_left hmaj hC0
        refine h1.trans ?_
        have h2 : raw offset ≤ theta M * ((nativeSourceRawFrame offset : ℚ) : ℝ) := hraw_le
        have hc : (0 : ℝ) ≤ (nativeC0 : ℝ) * ((1285 + 2 : ℕ) : ℝ) ^ 4 * (9 / 10 : ℝ) ^ (1285 + 1) *
            (((Nat.factorial 4 : ℕ) : ℝ) * 10 ^ 5) := by positivity
        have := mul_le_mul_of_nonneg_left h2 hc
        push_cast at this ⊢
        nlinarith [this]


/-- Theta scaling of the finite weighted sum: dividing the terms by `τ` reduces to the endpoint
finite sum. -/
theorem nativeReturns_finite_sum_theta (U : ℕ → ℝ≥0∞) (offset : ℕ) {τ : ℝ} (hτ : 0 < τ)
    (xs : List ℚ) (start : ℕ) (hxs : ∀ t ∈ xs, 0 ≤ t) (hlen : offset + start + xs.length ≤ 1335)
    (hterm : ∀ i < xs.length, U (start + i) ≤ ENNReal.ofReal (τ * nativeFrameReal
      (((11 / 10) * (2 * nativeGamma * ((offset + start + i : ℕ) : ℚ)) : ℚ) : ℝ)
        ((xs.getD i 0 : ℚ) : ℝ))) :
    ENNReal.ofReal (nativeC0 : ℝ) * ∑ i ∈ Finset.range xs.length,
        ENNReal.ofReal ((nativeHistoryRatio : ℝ) ^ (start + i)) * U (start + i) ≤
      ENNReal.ofReal (τ * nativeHistoryReal offset start xs) := by
  have h0 : ENNReal.ofReal τ ≠ 0 := (ENNReal.ofReal_pos.mpr hτ).ne'
  have htop : ENNReal.ofReal τ ≠ ⊤ := ENNReal.ofReal_ne_top
  let U' : ℕ → ℝ≥0∞ := fun r => (ENNReal.ofReal τ)⁻¹ * U r
  have hU : ∀ r, U r = ENNReal.ofReal τ * U' r := by
    intro r
    simp only [U']
    rw [← mul_assoc, ENNReal.mul_inv_cancel h0 htop, one_mul]
  have hterm' : ∀ i < xs.length, U' (start + i) ≤ ENNReal.ofReal (nativeFrameReal
      (((11 / 10) * (2 * nativeGamma * ((offset + start + i : ℕ) : ℚ)) : ℚ) : ℝ)
        ((xs.getD i 0 : ℚ) : ℝ)) := by
    intro i hi
    have h1 := hterm i hi
    rw [ENNReal.ofReal_mul hτ.le] at h1
    simp only [U']
    calc (ENNReal.ofReal τ)⁻¹ * U (start + i)
        ≤ (ENNReal.ofReal τ)⁻¹ * (ENNReal.ofReal τ * ENNReal.ofReal (nativeFrameReal
            (((11 / 10) * (2 * nativeGamma * ((offset + start + i : ℕ) : ℚ)) : ℚ) : ℝ)
              ((xs.getD i 0 : ℚ) : ℝ))) := mul_le_mul' le_rfl h1
      _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]
  have key := nativeReturns_finite_sum U' offset xs start hxs hlen hterm'
  calc ENNReal.ofReal (nativeC0 : ℝ) * ∑ i ∈ Finset.range xs.length,
        ENNReal.ofReal ((nativeHistoryRatio : ℝ) ^ (start + i)) * U (start + i)
      = ENNReal.ofReal τ * (ENNReal.ofReal (nativeC0 : ℝ) * ∑ i ∈ Finset.range xs.length,
        ENNReal.ofReal ((nativeHistoryRatio : ℝ) ^ (start + i)) * U' (start + i)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hU (start + i)]
        ring
    _ ≤ ENNReal.ofReal τ * ENNReal.ofReal (nativeHistoryReal offset start xs) :=
        mul_le_mul' le_rfl key
    _ = ENNReal.ofReal (τ * nativeHistoryReal offset start xs) :=
        (ENNReal.ofReal_mul hτ.le).symm

theorem nativeReturns_entry_nonneg_theta (M : ABKModel 2) (hz : M.gamma ≤ gammaZero) (g : ℕ)
    (hg9 : 9 ≤ g) (hg : g ≤ 1334) : 0 ≤ nativeReturnsEntry g := by
  unfold nativeReturnsEntry
  split_ifs with h160
  · have := nativeHeatResultGen_fst_nonneg g hg9 h160
    rwa [nativeHeatResultGen_eq_table g hg9 h160] at this
  · have := nativeReturns_raw_entry_nonneg_theta M hz g hg
    exact_mod_cast this

/-- The term of total gap `g` is bounded through the certified entry. -/
theorem nativeReturns_term_entry_theta (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hz : M.gamma ≤ gammaZero) (N : ℤ) (hN : ∀ n < N, nativeInductionState M h n) (g : ℕ)
    (hg9 : 9 ≤ g) (hg : g ≤ 1334) :
    eLpNorm (cutoffTraceDefect M N (N - ((g - 9 : ℕ) : ℤ))) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M * nativeFrameReal (((11 / 10) * (2 * nativeGamma * (g : ℚ)) : ℚ) : ℝ)
        ((nativeReturnsEntry g : ℚ) : ℝ)) := by
  unfold nativeReturnsEntry
  split_ifs with h160
  · have hq0 := nativeHeatResultGen_fst_nonneg g hg9 h160
    have := nativeReturns_term_heat_theta g hg9 h160 M h hM hz N hN hq0
    rw [nativeHeatResultGen_eq_table g hg9 h160] at this
    exact this
  · exact nativeReturns_term_raw_theta g hg9 hg M h hM hz N hN

theorem nativeReturns_xs_nonneg_theta (M : ABKModel 2) (hz : M.gamma ≤ gammaZero) (offset : ℕ)
    (hoff9 : 9 ≤ offset) (hoff : offset ≤ 49) (xs : List ℚ) (hlen : xs.length = 1286)
    (hentry : ∀ i < 1286, xs.getD i 0 = nativeReturnsEntry (offset + i)) :
    ∀ t ∈ xs, 0 ≤ t := by
  intro t ht
  obtain ⟨i, hi, hit⟩ := List.mem_iff_getElem.mp ht
  have hi' : i < 1286 := by omega
  have := hentry i hi'
  rw [List.getD_eq_getElem _ _ hi] at this
  rw [← hit, this]
  exact nativeReturns_entry_nonneg_theta M hz (offset + i) (by omega) (by omega)

/-- The generic bound of a weighted history by the certified sum plus tail. -/
theorem nativeReturns_history_bound_theta (M : ABKModel 2) (hz : M.gamma ≤ gammaZero) (offset : ℕ)
    (hoff9 : 9 ≤ offset) (hoff : offset ≤ 49) (xs : List ℚ) (hlen : xs.length = 1286)
    (hentry : ∀ i < 1286, xs.getD i 0 = nativeReturnsEntry (offset + i))
    (U : ℕ → ℝ≥0∞)
    (hterm : ∀ i < 1286, U i ≤ ENNReal.ofReal (theta M * nativeFrameReal
      (((11 / 10) * (2 * nativeGamma * ((offset + i : ℕ) : ℚ)) : ℚ) : ℝ)
        ((nativeReturnsEntry (offset + i) : ℚ) : ℝ)))
    (htail : ∀ r, 1286 ≤ r → U r ≤
      ENNReal.ofReal (nativeSourceExponentialRawFrame M.gamma (theta M) (offset + r))) :
    ENNReal.ofReal (nativeC0 : ℝ) * ∑' r : ℕ, ENNReal.ofReal ((nativeHistoryRatio : ℝ) ^ r) * U r ≤
      ENNReal.ofReal (theta M * (nativeHistoryReal offset 0 xs + ((nativeSourceHistoryTail offset : ℚ) : ℝ))) := by
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hz
  have hxs := nativeReturns_xs_nonneg_theta M hz offset hoff9 hoff xs hlen hentry
  have hfin := nativeReturns_finite_sum_theta U offset hτ0 xs 0 hxs (by omega) (by
    intro i hi
    have hi' : i < 1286 := by omega
    have h1 := hterm i hi'
    rw [← hentry i hi'] at h1
    simpa using h1)
  have htl := nativeReturns_tail_bound_theta M hz offset (by omega) hoff U htail
  have hEN : Summable (fun j : ℕ => ENNReal.ofReal ((nativeHistoryRatio : ℝ) ^ (j + 1286)) *
      U (j + 1286)) := ENNReal.summable
  have hsplit := hEN.sum_add_tsum_nat_add' (f := fun j : ℕ =>
    ENNReal.ofReal ((nativeHistoryRatio : ℝ) ^ j) * U j) (k := 1286)
  rw [← hsplit, mul_add]
  have h0 : 0 ≤ nativeHistoryReal offset 0 xs :=
    nativeReturns_historyReal_nonneg offset xs 0 hxs (by omega)
  have ht0 : (0 : ℝ) ≤ ((nativeSourceHistoryTail offset : ℚ) : ℝ) := by
    have hrf : (0 : ℝ) ≤ ((nativeSourceRawFrame offset : ℚ) : ℝ) := by
      have h1 := (native_source_actual_exponential_raw_frame_nonneg M offset).trans
        (nativeReturns_rawExp_theta_le_rat M hz offset (by omega))
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_pos_of_neg hτ0 hneg
      linarith
    have hC : (0 : ℝ) ≤ nativeC0 := by norm_num [nativeC0]
    unfold nativeSourceHistoryTail
    push_cast
    have := mul_nonneg hC hrf
    positivity
  rw [mul_add, ENNReal.ofReal_add (mul_nonneg hτ0.le h0) (mul_nonneg hτ0.le ht0)]
  refine add_le_add ?_ htl
  rw [← hlen]
  simpa using hfin


end ASDExplicitGamma.Native
