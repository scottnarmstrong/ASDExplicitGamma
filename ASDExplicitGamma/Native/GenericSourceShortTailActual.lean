module

public import ASDExplicitGamma.Native.GenericSourceShortTailData
public import ASDExplicitGamma.Native.GenericSourceDepthRows

/-! Complete actual-law mean tails and rare trace companion sums. The
extended series retain all infinite values until their finiteness is proved. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Domination by the complete raw series bounds an extended weighted tail.
Real summability is established before any ofReal-tsum conversion. -/
theorem native_source_short_raw_tail_ennreal
    (gamma theta : ℝ) (H J : ℕ) (hg0 : 0 ≤ gamma) (hg : gamma ≤ 17/50000)
    (ht : 0 ≤ theta) (hH : 1 ≤ H) (U : ℕ → ℝ≥0∞)
    (hcap : ∀ j, U j ≤ ENNReal.ofReal (nativeSourceExponentialRawFrame gamma theta (H+J+j))) :
    (∑' j : ℕ, ENNReal.ofReal (nativeSourceHistoryWeight gamma^(J+j))*U j) ≤
      ENNReal.ofReal (25*nativeSourceHistoryWeight gamma^J*
        nativeSourceExponentialRawFrame gamma theta (H+J)) := by
  have hs := native_source_short_raw_tail gamma theta H J hg0 hg ht hH
  have hq := (native_source_history_weight_endpoint_and_ratio gamma hg0 hg).1
  have h0 (j : ℕ) : 0 ≤ nativeSourceHistoryWeight gamma^(J+j)*
      nativeSourceExponentialRawFrame gamma theta (H+J+j) :=
    mul_nonneg (pow_nonneg hq _) (native_source_exponential_raw_nonneg gamma theta _ hg0 ht)
  calc
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (nativeSourceHistoryWeight gamma^(J+j)*
        nativeSourceExponentialRawFrame gamma theta (H+J+j)) := by
      apply ENNReal.tsum_le_tsum
      intro j
      rw [ENNReal.ofReal_mul (pow_nonneg hq _)]
      exact mul_le_mul' le_rfl (hcap j)
    _ = ENNReal.ofReal (∑' j : ℕ, nativeSourceHistoryWeight gamma^(J+j)*
        nativeSourceExponentialRawFrame gamma theta (H+J+j)) :=
      (ENNReal.ofReal_tsum_of_nonneg h0 hs.1).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hs.2

/-- The full actual weighted L20 companion sum has the outward allowance
used in the rational weak-row certificate. It includes every depth. -/
theorem native_source_complete_trace_companion_aux
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (r : Fin 6) :
    (∑' j : ℕ, ENNReal.ofReal (nativeSourceHistoryWeight M.gamma^j)*
      eLpNorm (cutoffTraceDefect M m (m-((r.val+j:ℕ):ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (theta M*(10^12:ℝ)) := by
  let H := 9+r.val
  have hg0 := M.shellPrefix.gamma_pos.le
  have ht : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  have hraw := native_source_short_raw_tail_ennreal M.gamma (theta M) H 0 hg0 hg ht (by dsimp [H]; omega)
    (fun j => eLpNorm (cutoffTraceDefect M m (m-((r.val+j:ℕ):ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure)
    (fun j => by
      simpa only [H,Nat.add_zero,Nat.add_assoc] using
        native_source_depth_exponential_eLpNorm M h hM hg m hpast (r.val+j))
  simp only [Nat.zero_add,pow_zero,mul_one,Nat.add_zero] at hraw
  have hbase := (native_source_exponential_raw_frame_le_generic M.gamma (theta M) H hg0 hg ht (by dsimp [H]; omega)).trans
    (native_source_generic_raw_frame_degree M.gamma (theta M) H hg0 hg rfl (by dsimp [H]; omega))
  have hnum : 25*nativeSourceGenericRawFrame (17/50000) 1 H ≤ (10^12:ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (native_source_whole_trace_endpoint_numeric r)
    norm_num only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow,native_source_rational_raw_endpoint_cast] at hh
    simpa only [H,show (10:ℝ)^12=1000000000000 by norm_num] using hh
  apply hraw.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ 25*(theta M*nativeSourceGenericRawFrame (17/50000) 1 H) := mul_le_mul_of_nonneg_left hbase (by norm_num)
    _ = theta M*(25*nativeSourceGenericRawFrame (17/50000) 1 H) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hnum ht

/-- The complete actual mean tail after gap 64 is paid by the positive
10^-5 allowance, uniformly on every smaller-gamma ray and all six offsets. -/
theorem native_source_complete_mean_tail_aux
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (r : Fin 6) :
    (∑' j : ℕ, ENNReal.ofReal (nativeSourceHistoryWeight M.gamma^(56-r.val+j))*
      nativeCompletedSourceMean M m (r.val+(56-r.val)+j)) ≤
      ENNReal.ofReal (theta M*(1/100000:ℝ)) := by
  let H := 9+r.val
  let J := 56-r.val
  have hbase : H+J=65 := by dsimp [H,J]; omega
  have hg0 := M.shellPrefix.gamma_pos.le
  have ht : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  have hraw := native_source_short_raw_tail_ennreal M.gamma (theta M) H J hg0 hg ht (by dsimp [H]; omega)
    (fun j => nativeCompletedSourceMean M m (r.val+J+j))
    (fun j => by
      simpa only [H,Nat.add_assoc] using
        native_source_depth_exponential_mean_ennreal M h hM hg m hpast (r.val+J+j))
  rw [hbase] at hraw
  have hpoint := (native_source_exponential_raw_frame_le_generic M.gamma (theta M) 65 hg0 hg ht (by norm_num)).trans
    (native_source_generic_raw_frame_degree M.gamma (theta M) 65 hg0 hg rfl (by norm_num))
  have hw := native_source_history_weight_endpoint_and_ratio M.gamma hg0 hg
  have hp := pow_le_pow_left₀ hw.1 hw.2.1 J
  have hF := native_source_generic_raw_frame_nonneg (17/50000) 1 65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnum : 25*nativeSourceHistoryWeight (17/50000)^J*nativeSourceGenericRawFrame (17/50000) 1 65 ≤ (1/100000:ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (native_source_short_tail_endpoint_numeric r)
    norm_num only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow,Rat.cast_div,
      native_source_rational_history_weight_cast,native_source_rational_raw_endpoint_cast] at hh
    exact hh
  apply hraw.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ 25*nativeSourceHistoryWeight M.gamma^J*(theta M*nativeSourceGenericRawFrame (17/50000) 1 65) :=
      mul_le_mul_of_nonneg_left hpoint (mul_nonneg (by norm_num) (pow_nonneg hw.1 J))
    _ ≤ 25*nativeSourceHistoryWeight (17/50000)^J*(theta M*nativeSourceGenericRawFrame (17/50000) 1 65) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (mul_nonneg ht hF)
    _ = theta M*(25*nativeSourceHistoryWeight (17/50000)^J*nativeSourceGenericRawFrame (17/50000) 1 65) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hnum ht

end
end ASDExplicitGamma.Native
