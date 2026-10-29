module

public import ASDExplicitGamma.Native.ReturnsTerms
public import ASDExplicitGamma.Native.ReturnsLists
public import ASDExplicitGamma.Native.GenericSourceSeriesEnvelope
public import ASDExplicitGamma.Statements.Strong20
public import ASDExplicitGamma.Statements.Buffer40History
public import ASDExplicitGamma.Numerics.Native.Returns

/-! NA-RETURNS: the complete frozen histories `strong20` and `buffer40History` are bounded by the
certified history sums (finite prefix of `1286` terms through the heat returns and the OLD raw
envelope, plus the closed raw tail). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Native ASDExplicitGamma.Variational
open scoped ENNReal

theorem nativeReturns_domain (n : ℕ) (hn : n ≤ 1334) :
    0 ≤ (((11 / 10) * (2 * nativeGamma * (n : ℚ)) : ℚ) : ℝ) ∧
      (((11 / 10) * (2 * nativeGamma * (n : ℚ)) : ℚ) : ℝ) < 1 := by
  have hnR : (n : ℝ) ≤ 1334 := by exact_mod_cast hn
  constructor
  · push_cast; norm_num [nativeGamma]
  · push_cast; norm_num [nativeGamma]; nlinarith

theorem nativeReturns_historyReal_nonneg (offset : ℕ) :
    ∀ (xs : List ℚ) (start : ℕ), (∀ t ∈ xs, 0 ≤ t) → offset + start + xs.length ≤ 1335 →
      0 ≤ nativeHistoryReal offset start xs := by
  intro xs
  induction xs with
  | nil => intro start _ _; simp [nativeHistoryReal]
  | cons t ts ih =>
    intro start hxs hlen
    have hts : ∀ u ∈ ts, 0 ≤ u := fun u hu => hxs u (List.mem_cons_of_mem _ hu)
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast hxs t List.mem_cons_self
    have hlen' : offset + (start + 1) + ts.length ≤ 1335 := by
      simp only [List.length_cons] at hlen; omega
    have hd := nativeReturns_domain (offset + start) (by simp only [List.length_cons] at hlen; omega)
    have hC : (0 : ℝ) ≤ nativeC0 := by norm_num [nativeC0]
    have hQ : (0 : ℝ) ≤ nativeHistoryRatio := by norm_num [nativeHistoryRatio]
    simp only [nativeHistoryReal]
    have hf := nativeFrameReal_nonneg _ _ hd.1 hd.2 ht0
    have := ih (start + 1) hts hlen'
    push_cast at hf ⊢
    positivity

theorem nativeReturns_finite_sum (U : ℕ → ℝ≥0∞) (offset : ℕ) :
    ∀ (xs : List ℚ) (start : ℕ), (∀ t ∈ xs, 0 ≤ t) → offset + start + xs.length ≤ 1335 →
    (∀ i < xs.length, U (start + i) ≤ ENNReal.ofReal (nativeFrameReal
      (((11 / 10) * (2 * nativeGamma * ((offset + start + i : ℕ) : ℚ)) : ℚ) : ℝ)
        ((xs.getD i 0 : ℚ) : ℝ))) →
    ENNReal.ofReal (nativeC0 : ℝ) * ∑ i ∈ Finset.range xs.length,
        ENNReal.ofReal ((nativeHistoryRatio : ℝ) ^ (start + i)) * U (start + i) ≤
      ENNReal.ofReal (nativeHistoryReal offset start xs) := by
  intro xs
  induction xs with
  | nil => intro start _ _ _; simp [nativeHistoryReal]
  | cons t ts ih =>
    intro start hxs hlen hterm
    have hts : ∀ u ∈ ts, 0 ≤ u := fun u hu => hxs u (List.mem_cons_of_mem _ hu)
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast hxs t List.mem_cons_self
    have hlen1 : offset + start + ts.length + 1 ≤ 1335 := by
      simp only [List.length_cons] at hlen; omega
    have hlen' : offset + (start + 1) + ts.length ≤ 1335 := by omega
    have ih' := ih (start + 1) hts hlen' (by
      intro i hi
      have h1 := hterm (i + 1) (by simpa using hi)
      have e1 : start + 1 + i = start + (i + 1) := by omega
      have e2 : offset + (start + 1) + i = offset + start + (i + 1) := by omega
      rw [e1, e2]
      rw [List.getD_cons_succ] at h1
      exact h1)
    have ih'' : ENNReal.ofReal (nativeC0 : ℝ) * ∑ i ∈ Finset.range ts.length,
        ENNReal.ofReal ((nativeHistoryRatio : ℝ) ^ (start + (i + 1))) * U (start + (i + 1)) ≤
        ENNReal.ofReal (nativeHistoryReal offset (start + 1) ts) := by
      simpa only [show ∀ i, start + 1 + i = start + (i + 1) from fun i => by omega] using ih'
    have hhead := hterm 0 (by simp)
    simp only [Nat.add_zero, List.getD_cons_zero] at hhead
    have hd := nativeReturns_domain (offset + start) (by omega)
    have hC : (0 : ℝ) ≤ nativeC0 := by norm_num [nativeC0]
    have hQ : (0 : ℝ) ≤ nativeHistoryRatio := by norm_num [nativeHistoryRatio]
    have hf := nativeFrameReal_nonneg _ _ hd.1 hd.2 ht0
    have hy0 := nativeReturns_historyReal_nonneg offset ts (start + 1) hts hlen'
    have hx0 : 0 ≤ (nativeC0 : ℝ) * (nativeHistoryRatio : ℝ) ^ start *
        nativeFrameReal (((11 / 10) * (2 * nativeGamma * ((offset + start : ℕ) : ℚ)) : ℚ) : ℝ)
          (t : ℝ) := by
      have := mul_nonneg (mul_nonneg hC (pow_nonneg hQ start)) hf
      exact this
    have hrec : nativeHistoryReal offset start (t :: ts) =
        (nativeC0 : ℝ) * (nativeHistoryRatio : ℝ) ^ start *
          nativeFrameReal (((11 / 10) * (2 * nativeGamma * ((offset + start : ℕ) : ℚ)) : ℚ) : ℝ)
            (t : ℝ) + nativeHistoryReal offset (start + 1) ts := by
      simp only [nativeHistoryReal]
    rw [hrec, ENNReal.ofReal_add hx0 hy0, List.length_cons, Finset.sum_range_succ']
    simp only [Nat.add_zero]
    have hsplit : ∀ S f0 : ℝ≥0∞, ENNReal.ofReal (nativeC0 : ℝ) * (S + f0) =
        ENNReal.ofReal (nativeC0 : ℝ) * f0 + ENNReal.ofReal (nativeC0 : ℝ) * S := by
      intro S f0; ring
    rw [hsplit]
    refine add_le_add ?_ ih''
    calc ENNReal.ofReal (nativeC0 : ℝ) * (ENNReal.ofReal ((nativeHistoryRatio : ℝ) ^ start) * U start)
        ≤ ENNReal.ofReal (nativeC0 : ℝ) * (ENNReal.ofReal ((nativeHistoryRatio : ℝ) ^ start) *
          ENNReal.ofReal (nativeFrameReal
            (((11 / 10) * (2 * nativeGamma * ((offset + start : ℕ) : ℚ)) : ℚ) : ℝ) (t : ℝ))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hhead)
      _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg hC (pow_nonneg hQ start)), ENNReal.ofReal_mul hC]
        ring

/-- The frozen discount and weight are below the certified constants. -/
theorem nativeReturns_weight_le (r : ℕ) :
    (3 : ℝ) ^ (-(3 / 20 : ℝ) * (r : ℝ)) ≤ (nativeHistoryRatio : ℝ) ^ r := by
  have h1 : (3 : ℝ) ^ (-(3 / 20 : ℝ) * (r : ℝ)) = ((3 : ℝ) ^ (-(3 / 20 : ℝ))) ^ r := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have h2 : (3 : ℝ) ^ (-(3 / 20 : ℝ)) ≤ nativeHistoryRatio := by
    have := native_history_ratio_real
    rw [show -(3 / 20 : ℝ) = -3 / 20 by norm_num]
    exact this.le
  rw [h1]
  exact pow_le_pow_left₀ (by positivity) h2 r

theorem nativeReturns_alpha_le : 1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (nativeC0 : ℝ) := by
  have := native_history_C0_real
  rw [show -(1 / 4 : ℝ) = -1 / 4 by norm_num]
  exact this.le

/-- The exponential raw frame is below the rational raw frame of the numerics. -/
theorem nativeReturns_rawExp_le_rat (M : ABKModel 2) (hz : M.gamma = gammaZero) (g : ℕ)
    (hg : g ≤ 1334) :
    nativeSourceExponentialRawFrame M.gamma (theta M) g ≤ ((nativeSourceRawFrame g : ℚ) : ℝ) := by
  have hγ : M.gamma = 17 / 50000 := by rw [hz]; rfl
  have hgR : (g : ℝ) ≤ 1334 := by exact_mod_cast hg
  have hin := nativeReturns_rawInput_le M hz g hg
  have hin0 : 0 ≤ nativeSourceExponentialRawFrameInput M.gamma (theta M) g := by
    have hγ0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
    have ht0 : 0 ≤ theta M := div_nonneg hγ0 (by norm_num [gammaZero])
    dsimp only [nativeSourceExponentialRawFrameInput, nativeSourceExponentialRawIncrement,
      nativeSourceExponentialVarianceCap, nativeSourceExponentialFullResponseCap,
      nativeSourceAverageFactor, nativeSourceRawMomentIncrement, nativeSourceK, nativeSourceM,
      nativeSourceQ, nativeSourceB128]
    positivity
  have hE := nativeReturns_three_pow_le_E (2 * (g : ℝ) * M.gamma) (by positivity)
    (by rw [hγ]; nlinarith)
  have hEq : (1 - (11 / 10 : ℝ) * (2 * (g : ℝ) * M.gamma))⁻¹ =
      (((nativeE (2 * nativeGamma * (g : ℚ)) : ℚ)) : ℝ) := by
    rw [hγ]; norm_num [nativeE, nativeGamma]; ring_nf
  rw [hEq] at hE
  unfold nativeSourceExponentialRawFrame nativeSourceRawFrame
  have hη : nativeSourceFrameEta = 1 / 1000 := rfl
  rw [hη]
  push_cast
  have hE0 : (0 : ℝ) ≤ (((nativeE (2 * nativeGamma * (g : ℚ)) : ℚ)) : ℝ) := by
    norm_num [nativeE, nativeGamma]
    have : (11 / 10 : ℝ) * (2 * (17 / 50000) * (g : ℝ)) < 1 := by nlinarith
    nlinarith
  have hsec : 8 * (1 + 1 / ((1 : ℝ) / 1000)) * ((11 / 10 : ℝ) * M.gamma * (g : ℝ)) ^ 2 =
      8 * (1 + 1000) * ((11 / 10 : ℝ) * (nativeGamma : ℝ) * (g : ℝ)) ^ 2 := by
    rw [hγ]; norm_num [nativeGamma]
  rw [hsec]
  have hin' : nativeSourceExponentialRawFrameInput M.gamma (theta M) g ≤
      (nativeAvg : ℝ) * (nativeA : ℝ) + ((nativeRaw g).2.2 : ℝ) := by
    simpa using hin
  refine mul_le_mul hE ?_ (by positivity) hE0
  have := mul_le_mul_of_nonneg_left hin' (by norm_num : (0 : ℝ) ≤ 1 + 1 / 1000)
  linarith

end ASDExplicitGamma.Native
