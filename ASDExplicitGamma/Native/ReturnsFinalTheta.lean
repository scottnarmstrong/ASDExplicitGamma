module

public import ASDExplicitGamma.Native.ReturnsMeanTheta
public import ASDExplicitGamma.Native.ReturnsFinal
public import ASDExplicitGamma.Native.ThetaScaledReturn

/-! NA-THETA-SCALING: the four native returns at target `N` for every `0 < γ ≤ γ₀` scale by `θ`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Native ASDExplicitGamma.Variational
open scoped ENNReal

theorem nativeReturns_strong20_theta_le (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hz : M.gamma ≤ gammaZero) (N : ℤ) (hN : ∀ n < N, nativeInductionState M h n) :
    strong20 M N ≤ ENNReal.ofReal (theta M * nativeSourceStrongHistory) := by
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
  have := nativeReturns_history_bound_theta M hz 9 le_rfl (by norm_num)
    nativeHistoryStrongCompletePrefix41 hlen hentry U
    (by
      intro i hi
      have h2 := nativeReturns_term_entry_theta M h hM hz N hN (9 + i) (by omega) (by omega)
      rw [show 9 + i - 9 = i by omega] at h2
      exact h2)
    (by
      intro r hr
      have h3 := native_source_depth_exponential_eLpNorm M h hM hz N (fun k hk => hN k hk) r
      exact h3)
  exact this

theorem nativeReturns_buffer40History_theta_le (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hz : M.gamma ≤ gammaZero) (N : ℤ) (hN : ∀ n < N, nativeInductionState M h n) :
    buffer40History M N ≤ ENNReal.ofReal (theta M * nativeSourceBufferHistory) := by
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
  have := nativeReturns_history_bound_theta M hz 49 (by norm_num) le_rfl
    nativeHistoryBufferCompletePrefix41 hlen hentry U
    (by
      intro i hi
      have h2 := nativeReturns_term_entry_theta M h hM hz N hN (49 + i) (by omega) (by omega)
      have e1 : N - (((49 + i - 9 : ℕ)) : ℤ) = N - 40 - (i : ℤ) := by
        rw [show 49 + i - 9 = 40 + i by omega]; push_cast; ring
      rw [e1] at h2
      exact h2)
    (by
      intro r hr
      have h3 := native_source_depth_exponential_eLpNorm M h hM hz N (fun k hk => hN k hk) (40 + r)
      have e1 : N - ((40 + r : ℕ) : ℤ) = N - 40 - (r : ℤ) := by push_cast; ring
      rw [e1, show 9 + (40 + r) = 49 + r by omega] at h3
      exact h3)
  exact this

theorem nativeReturns_root20_theta_le (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgam : M.gamma ≤ gammaZero) (N : ℤ) (hN : ∀ n < N, nativeInductionState M h n) :
    root20 M N ≤ ENNReal.ofReal (theta M * nativeFrameReal
      (((11 / 10) * (2 * nativeGamma * (9 : ℕ)) : ℚ) : ℝ) (nativeHeat009Result.1 : ℝ)) := by
  have hq0 : 0 ≤ (nativeHeatResultGen 9).1 := nativeHeatResultGen_fst_nonneg 9 le_rfl (by norm_num)
  have := nativeReturns_term_heat_theta 9 le_rfl (by norm_num) M h hM hgam N hN hq0
  rw [nativeHeatResultGen_009] at this
  simpa [root20] using this

/-- NA-THETA-SCALING: for every `0 < γ ≤ γ₀`, the four native returns at the target label `N` are
below `θ ·` the certified sharp values, hence below the carried caps `θ ·` `2379/2500`,
`2013/10000`, `61/10`, `8/25`, from the states at the labels below `N`. -/
theorem nativeThetaScaling_node (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ) (hN : ∀ n < N, nativeInductionState M h n) :
    NativeThetaScaledReturns M N := by
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  have hs := nativeReturns_strong20_theta_le M h hM hg N hN
  have hb := nativeReturns_buffer40History_theta_le M h hM hg N hN
  have hr := nativeReturns_root20_theta_le M h hM hg N hN
  have hm := nativeReturns_bufferMean_theta M h hM hg N hN
  obtain ⟨n1, n2, n3, n4⟩ := native_all_sharp_return_values
  have lt : ∀ {x : ℝ≥0∞} {S c : ℝ}, 0 < c → x ≤ ENNReal.ofReal (theta M * S) → S < c →
      x < ENNReal.ofReal (c * theta M) := by
    intro x S c hc hx hSc
    refine lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff (mul_pos hc hτ0)).2 ?_)
    nlinarith
  have hstrong := lt (by norm_num) hs n1
  have hroot := lt (by norm_num) hr n2
  have hhist := lt (by norm_num) hb n3
  have hmean := lt (by norm_num) hm n4
  have hcaps := native_theta_scaled_carried_caps_of_sharp_returns M N hτ0.le hstrong hroot
    hhist hmean
  exact ⟨hstrong, hroot, hhist, hmean, hcaps.1, hcaps.2.1, hcaps.2.2.1, hcaps.2.2.2⟩

end ASDExplicitGamma.Native
