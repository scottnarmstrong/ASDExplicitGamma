module

public import ASDExplicitGamma.Native.OldSignedWeakShiftBound
public import ASDExplicitGamma.Native.OldSignedActualLocalHistory
public import ASDExplicitGamma.Native.OldSignedActualTiledProfiles
public import ASDExplicitGamma.Native.OldSignedHistoryBounds

/-! A coarse rare-only majorant of the actual tiled weak energy. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Gaussian Scalar Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- The full parent quarter-discounted raw trace, in the actual fixed frame. -/
def oldSignedActualQuarterTrace (M : ABKModel 2) (n : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  rawWeakTraceHistory (rawWeakTraceSequence M n (originCube 2 n) t ω)

/-- The untruncated quarter trace is pointwise nonnegative. -/
theorem old_signed_actual_quarter_trace_nonneg (M : ABKModel 2) (n : ℤ)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (ω : Cutoff.CutoffSample 2) :
    0≤oldSignedActualQuarterTrace M n t ω :=
  mul_nonneg (sub_nonneg.mpr inverse_history_discount_range.2.le)
    (tsum_nonneg (fun j => mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
      (raw_weak_trace_sequence_nonneg M n _ t ht ω j)))

/-- The root weak proxy is bounded by its true inverse history and trace. -/
theorem old_signed_actual_root_weak_majorant (M : ABKModel 2) (n : ℤ)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (ω : Cutoff.CutoffSample 2) :
    oldSignedActualTiledWeakProxy M n 0 t ω≤
      (1+inverseHistoryDiscount)*oldSignedInverseHistory (originCube 2 n)
        (oldSignedPartialFrameField M n 1 t ω)*oldSignedActualQuarterTrace M n t ω := by
  let Q := originCube 2 n
  let a := oldSignedPartialFrameField M n 1 t ω
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
    (oldSignedPartialResponseCoefficient n 1 t ω)
  have hdepth (j : ℕ) : inverseHistoryDiscount^j*lemmaVInverseDepthMax Q a j≤oldSignedInverseHistory Q a := by
    simpa only [one_mul,oldSignedInverseHistory] using actual_inverse_depth_discount_bound Q a hEll 1 (by norm_num) j
  have hs := old_signed_weak_trace_proxy_summable Q a hEll
  have hT := old_signed_trace_depth_series_summable Q a hEll
  simp_rw [Q,a,old_signed_one_shell_trace_depth] at hs hT
  simpa only [oldSignedActualTiledWeakProxy,Nat.zero_add,oldSignedActualQuarterTrace] using
    raw_weak_trace_proxy_le (lemmaVInverseDepthMax Q a)
      (rawWeakTraceSequence M n Q t ω) (oldSignedInverseHistory Q a) hdepth
      (raw_weak_trace_sequence_nonneg M n Q t ht ω) hs hT

/-- The mesh-five proxy is bounded by 32 times the common local history
and parent trace. This coarse estimate is reserved for rare monomials. -/
theorem old_signed_actual_q1_weak_rare_majorant
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l<n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      oldSignedActualTiledWeakProxy M n 5 t ω≤
        32*rawShellBandLocalHistory M n 1 t ω*oldSignedActualQuarterTrace M n t ω := by
  have hbank := old_signed_actual_cell_inverse_history_split M h hM hg n hpast 0 (by norm_num)
    (originCube 2 n) (by simp only [descendantsAtDepth_zero,Finset.mem_singleton]) t ht
  filter_upwards [hbank] with ω hω
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet (originCube 2 n))
    M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
    (oldSignedPartialResponseCoefficient n 1 t ω)
  have hs := old_signed_shifted_weak_proxy_le (originCube 2 n) 5 (oldSignedPartialFrameField M n 1 t ω) hEll
  simp_rw [old_signed_one_shell_trace_depth] at hs
  have hs' : oldSignedActualTiledWeakProxy M n 5 t ω≤
      (inverseHistoryDiscount^(2*5))⁻¹*oldSignedActualTiledWeakProxy M n 0 t ω := by
    simpa only [oldSignedActualTiledWeakProxy,Nat.zero_add] using hs
  have hH := old_signed_actual_quarter_trace_nonneg M n t ht ω
  have hD : 0≤1+inverseHistoryDiscount := add_nonneg (by norm_num) inverse_history_discount_range.1.le
  have hB0 : 0≤rawShellBandLocalHistory M n 1 t ω := ENNReal.toReal_nonneg
  have hroot := (old_signed_actual_root_weak_majorant M n t ht ω).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hω.1 hD) hH)
  calc
    _ ≤ (inverseHistoryDiscount^(2*5))⁻¹*((1+inverseHistoryDiscount)*rawShellBandLocalHistory M n 1 t ω*
        oldSignedActualQuarterTrace M n t ω) := hs'.trans (mul_le_mul_of_nonneg_left hroot
      (inv_nonneg.mpr (pow_nonneg inverse_history_discount_range.1.le _)))
    _ = ((inverseHistoryDiscount^(2*5))⁻¹*(1+inverseHistoryDiscount))*
        (rawShellBandLocalHistory M n 1 t ω*oldSignedActualQuarterTrace M n t ω) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right old_signed_q1_rare_shift_factor
      (mul_nonneg hB0 hH)).trans_eq (by ring)

end
end ASDExplicitGamma.Native
