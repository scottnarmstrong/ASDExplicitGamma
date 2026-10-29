module

public import ASDExplicitGamma.Native.ParentWeakTraceDomination
public import ASDExplicitGamma.Native.ParentBoundaryBandTraceMoments

/-! Theta-linear actual depth trace norms for correlated rare payments. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Coarse theta-linear depth allowance, used only multiplied by the original
bank remainder. Leading trace means are treated with their exact source law. -/
def parentWeakRareTraceCap (M : ABKModel 2) (j : ℕ) : ℝ :=
  (10:ℝ)^20*theta M*(inverseHistoryDiscount^j)⁻¹

/-- Positivity of the rare-only allowance. -/
theorem parent_weak_rare_trace_cap_nonneg (M : ABKModel 2) (j : ℕ) :
    0 ≤ parentWeakRareTraceCap M j := by
  unfold parentWeakRareTraceCap
  exact mul_nonneg (mul_nonneg (by norm_num) (cold_theta_pos M).le)
    (inv_nonneg.mpr (pow_nonneg inverse_history_discount_range.1.le _))

/-- Actual trace L2 on any protected source cell has one theta. No trace
norm or history estimate is a premise. -/
theorem parent_weak_cell_trace_L2
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height) (hh16 : height ≤ 16)
    (hpast : ∀ k<n,nativeInductionState M h k) (hstate : nativeInductionState M h n)
    (r : ℕ) (hr : r ≤ 5) (U : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) r) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (j : ℕ) :
    eLpNorm (parentBoundaryBandCellTrace M n height t U j) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((10:ℝ)^17*theta M*(inverseHistoryDiscount^j)⁻¹) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let H := fun ω => (parentBoundaryBandMaxTraceHistory M n height U t ω).toReal
  let c := 10*(inverseHistoryDiscount^j)⁻¹
  have hc : 0 ≤ c := mul_nonneg (by norm_num) (inv_nonneg.mpr (pow_nonneg inverse_history_discount_range.1.le _))
  have hscale : U.scale=n-(r:ℤ) := by
    simpa only [originCube] using scale_eq_sub_of_mem_descendantsAtDepth hU
  have hH := parent_weak_actual_history_L2 M h hM hg U n r hr hscale hstate height hheight hh16 hpast t ht
  have hT := parent_boundary_band_trace_sequence_integrable M h hM n height hheight r U hU t j
  have hpoint (ω) : parentBoundaryBandCellTrace M n height t U j ω ≤ c*H ω := by
    rw [←parent_boundary_band_cell_trace_eq M n height r U hU t ω j]
    dsimp only [H,c]
    rw [parent_boundary_band_max_trace_history_toReal M n height r U hU t ω]
    exact parent_weak_trace_depth_le_history U _
      ((responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet (originCube 2 n))
        M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
        (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω))).mono
        (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)) j
  have hmono : eLpNorm (parentBoundaryBandCellTrace M n height t U j) 2 μ ≤
      eLpNorm (fun ω => c*H ω) 2 μ := by
    apply eLpNorm_mono_ae_real hT.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_of_nonneg (show 0 ≤ parentBoundaryBandCellTrace M n height t U j ω from by
      unfold parentBoundaryBandCellTrace descendantsAverage
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg
        (fun V _ => parent_boundary_band_trace_nonneg M n height t V ω)))]
    exact hpoint ω
  rw [parent_history_nonneg_const_norm μ H 2 c hc] at hmono
  exact (hmono.trans (mul_le_mul_of_nonneg_left hH.2 (bot_le : (0:ℝ≥0∞)≤ENNReal.ofReal c))).trans_eq
    (by rw [←ENNReal.ofReal_mul hc]; congr 1; dsimp only [c]; ring)

/-- The depth-(r+j) trace on the whole parent has the same rare-only cap,
including all protected source roots r<=5. -/
theorem parent_weak_tiled_trace_L2
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height) (hh16 : height ≤ 16)
    (hpast : ∀ k<n,nativeInductionState M h k) (hstate : nativeInductionState M h n)
    (r : ℕ) (hr : r ≤ 5) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (j : ℕ) :
    eLpNorm (parentBoundaryBandCellTrace M n height t (originCube 2 n) (r+j)) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (parentWeakRareTraceCap M j) := by
  have hh := parent_weak_cell_trace_L2 M h hM hg n height hheight hh16 hpast hstate
    0 (by norm_num) (originCube 2 n) (by simp only [descendantsAtDepth_zero,Finset.mem_singleton]) t ht (r+j)
  have hp : (1/32:ℝ)≤ inverseHistoryDiscount^r := by
    calc
      _ = (1/2:ℝ)^5 := by norm_num
      _ ≤ (1/2:ℝ)^r := pow_le_pow_of_le_one (by norm_num) (by norm_num) hr
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) parent_weak_discount_range.1 _
  have hi : (inverseHistoryDiscount^r)⁻¹≤32 := by
    calc
      _ ≤ (1/32:ℝ)⁻¹ := inv_anti₀ (by norm_num) hp
      _ = _ := by norm_num
  apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
  unfold parentWeakRareTraceCap
  rw [pow_add,mul_inv_rev]
  calc
    _ = ((10:ℝ)^17*theta M*(inverseHistoryDiscount^j)⁻¹)*(inverseHistoryDiscount^r)⁻¹ := by ring
    _ ≤ ((10:ℝ)^17*theta M*(inverseHistoryDiscount^j)⁻¹)*32 :=
      mul_le_mul_of_nonneg_left hi (mul_nonneg (mul_nonneg (by norm_num) (cold_theta_pos M).le)
        (inv_nonneg.mpr (pow_nonneg inverse_history_discount_range.1.le _)))
    _ ≤ _ := by
      have hcoef : (10:ℝ)^17*32≤10^20 := by norm_num
      have hh := mul_le_mul_of_nonneg_right hcoef
        (mul_nonneg (cold_theta_pos M).le (inv_nonneg.mpr (pow_nonneg inverse_history_discount_range.1.le j)))
      convert hh using 1 <;> ring

end
end ASDExplicitGamma.Native
