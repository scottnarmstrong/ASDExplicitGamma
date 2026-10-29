module

public import ASDExplicitGamma.Native.ParentWeakTraceDomination
public import ASDExplicitGamma.Native.GenericSourceBandFactors

/-! Rare-only domination of the actual weak proxy by one common bank and
one complete physical maximum history on the same sample. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- The actual complete weak proxy is nonnegative at every sample. -/
theorem parent_weak_proxy_nonneg (M : ABKModel 2) (n : ℤ) (height depth : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ parentBoundaryBandWeakProxy M n height depth t ω := by
  unfold parentBoundaryBandWeakProxy rawWeakTraceProxy
  apply mul_nonneg (sub_nonneg.mpr
    (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le))
  apply tsum_nonneg
  intro j
  apply mul_nonneg (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _) ENNReal.toReal_nonneg)
  unfold parentBoundaryBandTraceDepth descendantsAverage
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg
    (fun V _ => parent_boundary_band_trace_nonneg M n height t V ω))

/-- Uniform protected-depth shift loss, reserved for rare products. -/
theorem parent_weak_rare_shift_factor (depth : ℕ) (hdepth : depth ≤ 5) :
    (1+inverseHistoryDiscount)*(inverseHistoryDiscount^depth)⁻¹ ≤ 64 := by
  have hp : (1/32:ℝ)≤ inverseHistoryDiscount^depth := by
    calc
      _ = (1/2:ℝ)^5 := by norm_num
      _ ≤ (1/2:ℝ)^depth := pow_le_pow_of_le_one (by norm_num) (by norm_num) hdepth
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) parent_weak_discount_range.1 _
  have hi : (inverseHistoryDiscount^depth)⁻¹≤32 := by
    calc
      _ ≤ (1/32:ℝ)⁻¹ := inv_anti₀ (by norm_num) hp
      _ = _ := by norm_num
  have hd : 1+inverseHistoryDiscount ≤ 2 := by linarith only [inverse_history_discount_range.2]
  exact (mul_le_mul hd hi (inv_nonneg.mpr (pow_nonneg inverse_history_discount_range.1.le _))
    (by norm_num : (0:ℝ)≤2)).trans_eq (by norm_num)

/-- On the simultaneous band, W is dominated by 64 B H, using the actual
common bank B and complete physical history H. No independence is used. -/
theorem parent_weak_actual_rare_majorant
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height depth : ℕ) (hdepth : depth ≤ 5)
    (hpast : ∀ l<n,nativeInductionState M h l) (t : ℝ) (ht : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      parentBoundaryBandWeakProxy M n height depth t ω ≤
        64*(nativeSourceBandHistory M n height t ω).toReal*
          (parentBoundaryBandMaxTraceHistory M n height (originCube 2 n) t ω).toReal := by
  have hb := parent_boundary_actual_band_bank_proxy M h hM hg n height depth hdepth hpast t ht
  filter_upwards [hb] with ω hω
  let Q := originCube 2 n
  let a := parentBoundaryBandFrameField M n height t ω
  let B := (nativeSourceBandHistory M n height t ω).toReal
  let H := (parentBoundaryBandMaxTraceHistory M n height Q t ω).toReal
  have hroot : Q∈descendantsAtDepth Q 0 := by simp only [descendantsAtDepth_zero,Finset.mem_singleton]
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
    (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω))
  have hquarter : rawWeakTraceHistory (fun j => parentBoundaryBandTraceDepth M n height t ω (depth+j)) ≤
      (inverseHistoryDiscount^depth)⁻¹*H := by
    dsimp only [H]
    rw [parent_boundary_band_max_trace_history_toReal M n height 0 Q hroot t ω]
    simpa only [Q,a,parent_boundary_band_trace_depth] using
      parent_weak_shifted_trace_le_history Q a hEll depth
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
  calc
    _ ≤ (1+inverseHistoryDiscount)*B*((inverseHistoryDiscount^depth)⁻¹*H) :=
      hω.trans (mul_le_mul_of_nonneg_left hquarter
        (mul_nonneg (add_nonneg (by norm_num) inverse_history_discount_range.1.le) hB0))
    _ = ((1+inverseHistoryDiscount)*(inverseHistoryDiscount^depth)⁻¹)*(B*H) := by ring
    _ ≤ 64*(B*H) := mul_le_mul_of_nonneg_right (parent_weak_rare_shift_factor depth hdepth) (mul_nonneg hB0 hH0)
    _ = _ := by ring

end
end ASDExplicitGamma.Native
