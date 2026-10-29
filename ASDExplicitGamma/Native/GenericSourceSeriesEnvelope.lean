module

public import ASDExplicitGamma.Native.GenericSourceDepthRows

/-! Extended positive source series, retaining the full real raw tail and
its independently proved summability before any conversion to ENNReal. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The actual raw source series is summable with its complete covariance
and full-response tail. This rules out a default-zero real tsum. -/
theorem native_source_actual_raw_series_summable
    (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (H : ℕ) (hH : 1 ≤ H) :
    Summable (fun j : ℕ => (nativeSourceHistoryWeight M.gamma)^j*
      nativeSourceExponentialRawFrame M.gamma (theta M) (H+j)) := by
  let q := nativeSourceHistoryWeight M.gamma
  let growth := (3:ℝ)^(6*M.gamma)
  let raw := nativeSourceExponentialRawFrame M.gamma (theta M)
  have hg0 := M.shellPrefix.gamma_pos.le
  have ht0 : 0 ≤ theta M := div_nonneg hg0 (by norm_num [gammaZero])
  have hq0 : 0 ≤ q := (native_source_history_weight_endpoint_and_ratio M.gamma hg0 hg).1
  have hratio : q*growth ≤ (9/10:ℝ) :=
    (native_source_history_weight_endpoint_and_ratio M.gamma hg0 hg).2.2
  have hraw0 (j) : 0 ≤ raw j := native_source_actual_exponential_raw_frame_nonneg M j
  have hmajor := native_source_geom_quadratic_summable.mul_left (raw H)
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hq0 j) (hraw0 _)) _ hmajor
  intro j
  have hframe := native_source_exponential_raw_frame_growth M.gamma (theta M) H j hg0 ht0 hH
  have hpow := pow_le_pow_left₀ (mul_nonneg hq0 (by dsimp [growth]; positivity)) hratio j
  calc
    _ ≤ q^j*(raw H*((j+1:ℕ):ℝ)^2*growth^j) :=
      mul_le_mul_of_nonneg_left hframe (pow_nonneg hq0 j)
    _ = raw H*(((j:ℝ)+1)^2*(q*growth)^j) := by push_cast; rw [mul_pow]; ring
    _ ≤ raw H*(((j:ℝ)+1)^2*(9/10:ℝ)^j) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (sq_nonneg _)) (hraw0 H)

/-- A positive extended series with a certified finite prefix and the full
raw tail is controlled by their sum. No finiteness premise is imposed on the
actual sequence; the conclusion proves it. -/
theorem native_source_extended_series_envelope
    (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (r N : ℕ)
    (U : ℕ → ℝ≥0∞) (profile : ℕ → ℝ)
    (hprofile : ∀ j ≤ N, 0 ≤ profile j)
    (hfinite : ∀ j ≤ N, U j ≤ ENNReal.ofReal (profile j))
    (htail : ∀ j, N < j → U j ≤
      ENNReal.ofReal (nativeSourceExponentialRawFrame M.gamma (theta M) (9+r+j))) :
    (∑' j : ℕ, ENNReal.ofReal ((nativeSourceHistoryWeight M.gamma)^j)*U j) ≤
      ENNReal.ofReal
        (nativeSourceFiniteWeightedRow (nativeSourceHistoryWeight M.gamma) profile N+
          nativeSourceRawWeightedTail (nativeSourceHistoryWeight M.gamma) (9+r) N
            (nativeSourceExponentialRawFrame M.gamma (theta M))) := by
  let q := nativeSourceHistoryWeight M.gamma
  let raw := nativeSourceExponentialRawFrame M.gamma (theta M)
  have hg0 := M.shellPrefix.gamma_pos.le
  have hq0 : 0 ≤ q := (native_source_history_weight_endpoint_and_ratio M.gamma hg0 hg).1
  have hraw0 (j) : 0 ≤ raw j := native_source_actual_exponential_raw_frame_nonneg M j
  have hs := native_source_actual_raw_series_summable M hg (9+r) (by omega)
  change Summable (fun j : ℕ => q^j*raw (9+r+j)) at hs
  have hshift : Summable (fun j : ℕ => q^(N+1+j)*raw (9+r+(N+1+j))) := by
    have hh : Summable (fun j : ℕ => q^(j+(N+1))*raw (9+r+(j+(N+1)))) :=
      (summable_nat_add_iff (N+1)).mpr hs
    simpa only [Nat.add_comm] using hh
  have hpref : (∑ j ∈ Finset.range (N+1), ENNReal.ofReal (q^j)*U j) ≤
      ENNReal.ofReal (nativeSourceFiniteWeightedRow q profile N) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (N+1), ENNReal.ofReal (q^j*profile j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjN : j ≤ N := by have hh := Finset.mem_range.mp hj; omega
        rw [ENNReal.ofReal_mul (pow_nonneg hq0 j)]
        exact mul_le_mul' le_rfl (hfinite j hjN)
      _ = _ := by
        rw [nativeSourceFiniteWeightedRow,ENNReal.ofReal_sum_of_nonneg
          (fun j hj => mul_nonneg (pow_nonneg hq0 j) (hprofile j (by have hh := Finset.mem_range.mp hj; omega)))]
  have htailBound : (∑' j : ℕ, ENNReal.ofReal (q^(N+1+j))*U (N+1+j)) ≤
      ENNReal.ofReal (nativeSourceRawWeightedTail q (9+r) N raw) := by
    calc
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (q^(N+1+j)*raw (9+r+(N+1+j))) := by
        apply ENNReal.tsum_le_tsum
        intro j
        rw [ENNReal.ofReal_mul (pow_nonneg hq0 _)]
        exact mul_le_mul' le_rfl (htail (N+1+j) (by omega))
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg
        (fun j => mul_nonneg (pow_nonneg hq0 _) (hraw0 _)) hshift).symm
  have hEN : Summable (fun j : ℕ => ENNReal.ofReal (q^(j+(N+1)))*U (j+(N+1))) := ENNReal.summable
  have hsplit := hEN.sum_add_tsum_nat_add' (f := fun j : ℕ => ENNReal.ofReal (q^j)*U j) (k := N+1)
  rw [←hsplit]
  have hprefix0 : 0 ≤ nativeSourceFiniteWeightedRow q profile N :=
    Finset.sum_nonneg (fun j hj => mul_nonneg (pow_nonneg hq0 j) (hprofile j (by have hh := Finset.mem_range.mp hj; omega)))
  have htail0 : 0 ≤ nativeSourceRawWeightedTail q (9+r) N raw :=
    tsum_nonneg (fun j => mul_nonneg (pow_nonneg hq0 _) (hraw0 _))
  rw [ENNReal.ofReal_add hprefix0 htail0]
  exact add_le_add hpref (by simpa only [Nat.add_comm] using htailBound)

end
end ASDExplicitGamma.Native
