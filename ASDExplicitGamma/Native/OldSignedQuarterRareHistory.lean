module

public import ASDExplicitGamma.Native.OldSignedQuarterRareReserve
public import ASDExplicitGamma.Native.OldSignedBankRareHistory

/-! Complete rare history at the slower discount needed by bank-weighted OLD energies. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Cold Algsuperdiff.Section3 Numerics.Inverse
noncomputable section

/-- The entire actual rare history, through four correlated bank powers,
is integrable with a theta-scaled reserve even at the slower discount. -/
theorem old_signed_local_bank_quarter_rare_history
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (hpast : ∀ l≤n,nativeInductionState M h l) (k : ℕ) (hk : k≤4) :
    let f := fun ω => (1-inverseHistoryDiscount)*∑' j : ℕ,inverseHistoryDiscount^j*
      rareExpansionTail (3683/2500) (oldSignedLocalBankRemainder M n t ω)
        (rawWeakTraceSequence M n (originCube 2 n) t ω j) k
    Integrable f (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,f ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ (1/10^30:ℝ)*theta M := by
  let T := fun j ω => rawWeakTraceSequence M n (originCube 2 n) t ω j
  let f := fun j ω => inverseHistoryDiscount^j*
    rareExpansionTail (3683/2500) (oldSignedLocalBankRemainder M n t ω) (T j ω) k
  let C := fun j : ℕ => theta M*(invTraceM:ℝ)*(1+(j:ℝ))^2*(3:ℝ)^(6*gammaZero*j)
  have htheta : 0≤theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMr : 0 ≤ invTraceM := by rw [invTrace_coefficient.1]; positivity
  have hM0 : 0≤(invTraceM:ℝ) := by exact_mod_cast hMr
  have hC (j : ℕ) : 0≤C j := by dsimp [C]; positivity
  have hb := raw_shell_band_local_inverse_bank M h hM hg n 1 (by norm_num) t ht
    (fun l hl => hpast l hl.le)
  have hT (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0≤T j ω :=
    raw_weak_trace_sequence_nonneg M n (originCube 2 n) t ht ω j
  have hfn (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0≤f j ω := by
    dsimp [f,rareExpansionTail]
    apply mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity))
      (pow_nonneg (hb.remainder_nonneg ω) i)) (hT j ω)
  have hs (ω : Cutoff.CutoffSample 2) : Summable (fun j => f j ω) := by
    have hEll := responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet (originCube 2 n)) M.nu (Annealed.sigmaBar M n)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1 (oldSignedPartialResponseCoefficient n 1 t ω)
    have htrace := old_signed_trace_depth_series_summable (originCube 2 n)
      (oldSignedPartialFrameField M n 1 t ω) hEll
    simp_rw [old_signed_one_shell_trace_depth M n t ω] at htrace
    have hs2 : Summable (fun j => inverseHistoryDiscount^j*T j ω) := htrace
    have hh := hs2.mul_left (rareExpansionTail (3683/2500) (oldSignedLocalBankRemainder M n t ω) 1 k)
    apply hh.congr
    intro j
    dsimp [f]
    rw [old_signed_rare_tail_linear _ _ (T j ω) k]
    ring
  have hp (j : ℕ) := old_signed_local_bank_rare_power_tail M h hM hg n t ht hpast j k hk
  have hi (j : ℕ) : Integrable (f j) (Cutoff.cutoffSampleLaw M).toMeasure :=
    (hp j).1.const_mul _
  have hprofile := old_signed_quarter_trace_profile M
  have hbudget := hprofile.1.mul_left (13*(3/10^46:ℝ))
  have hh := old_signed_nonnegative_series_integral (Cutoff.cutoffSampleLaw M).toMeasure f
    (fun j => (13*(3/10^46:ℝ))*(inverseHistoryDiscount^j*C j))
    hi hfn hs hbudget (by
      intro j
      dsimp only [f]
      rw [integral_const_mul]
      exact (mul_le_mul_of_nonneg_left (hp j).2
        (pow_nonneg inverse_history_discount_range.1.le _)).trans_eq (by ring))
  have hw : 0≤1-inverseHistoryDiscount := sub_nonneg.mpr inverse_history_discount_range.2.le
  have hw1 : 1-inverseHistoryDiscount≤1 := sub_le_self _ inverse_history_discount_range.1.le
  refine ⟨hh.1.const_mul _,?_⟩
  change (∫ ω,(1-inverseHistoryDiscount)*∑' j,f j ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤_
  rw [integral_const_mul]
  have hbnd := mul_le_mul_of_nonneg_left hh.2 hw
  rw [tsum_mul_left] at hbnd
  have hpbound := mul_le_mul_of_nonneg_left hprofile.2
    (by norm_num : (0:ℝ)≤13*(3/10^46:ℝ))
  have hMcap : (invTraceM:ℝ)≤10^6 := by exact_mod_cast invTrace_coefficient.2.1.le
  have hc : 0≤(13*(3/10^46:ℝ))*(theta M*(invTraceM:ℝ)*1900) := by positivity
  calc
    _ ≤ (1-inverseHistoryDiscount)*((13*(3/10^46:ℝ))*(∑' j,inverseHistoryDiscount^j*C j)) := hbnd
    _ ≤ (1-inverseHistoryDiscount)*((13*(3/10^46:ℝ))*(theta M*(invTraceM:ℝ)*1900)) :=
      mul_le_mul_of_nonneg_left hpbound hw
    _ ≤ (13*(3/10^46:ℝ))*(theta M*(invTraceM:ℝ)*1900) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hw1 hc
    _ = ((13*(3/10^46:ℝ))*1900*theta M)*(invTraceM:ℝ) := by ring
    _ ≤ ((13*(3/10^46:ℝ))*1900*theta M)*10^6 := mul_le_mul_of_nonneg_left hMcap (by positivity)
    _ ≤ (1/10^30:ℝ)*theta M := by
      have hn : (13*(3/10^46:ℝ))*1900*10^6≤1/10^30 := by norm_num
      convert mul_le_mul_of_nonneg_right hn htheta using 1
      ring

end
end ASDExplicitGamma.Native
