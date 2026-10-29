module

public import ASDExplicitGamma.Native.ParentWeakBudget
public import ASDExplicitGamma.Native.ParentWeakTiledDepth
public import ASDExplicitGamma.Native.ParentBoundaryBandTiledDepthBank
public import ASDExplicitGamma.Native.ParentBoundaryBandHistoryStationarity
public import ASDExplicitGamma.Native.ParentBoundaryBandTraceMoments
public import ASDExplicitGamma.Native.OldSignedSourceDirectionalPayment
public import ASDExplicitGamma.Native.ParentBoundaryBandWeak
public import ASDExplicitGamma.Native.OldSignedNonnegativeSeriesIntegral

/-! The actual complete simultaneous-band weak proxy with a sharp theta return. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Cold Algsuperdiff.Section3
noncomputable section

/-- The actual whole-parent weak proxy has a finite expectation paid by
twice the common directional history budget, without a finiteness premise. -/
theorem parent_weak_actual_budget_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16) (r : ℕ) (hr : r=5)
    (U0 : TriadicCube 2) (hU0 : U0∈descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (hpast : ∀ k<n,nativeInductionState M h k) (hstate : nativeInductionState M h n) :
    Integrable (parentBoundaryBandWeakProxy M n height r t) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ omega,parentBoundaryBandWeakProxy M n height r t omega ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      2*((1-inverseHistoryDiscount^2)*∑' j : ℕ,inverseHistoryDiscount^(2*j)*
        parentWeakDirectionalBudget M n height U0 t j) := by
  let f := fun j omega => inverseHistoryDiscount^(2*j)*
    parentBoundaryBandInverseDepth M n height t omega (r+j)*
      parentBoundaryBandTraceDepth M n height t omega (r+j)
  have hs (omega) : Summable (fun j => f j omega) :=
    (parent_boundary_actual_band_weak_budget M n height r t omega).2.2
  have hbud := parent_weak_directional_budget_return M h hM hg n height hheight hpast hstate r hr U0 hU0 t ht
  have hp (j : ℕ) :
      Integrable (fun ω => lemmaVInverseDepthMax (originCube 2 n) (parentBoundaryBandFrameField M n height t ω) (r+j)*
        parentBoundaryBandCellTrace M n height t (originCube 2 n) (r+j) ω) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,lemmaVInverseDepthMax (originCube 2 n) (parentBoundaryBandFrameField M n height t ω) (r+j)*
        parentBoundaryBandCellTrace M n height t (originCube 2 n) (r+j) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          2*parentWeakDirectionalBudget M n height U0 t j := by
    have hh := parent_weak_tiled_depth_payment M h hM hg n height hheight hh16 r (by omega) U0 hU0 t ht hpast hstate j
    refine ⟨hh.1,hh.2.trans ?_⟩
    have heps : 0 ≤ inverseBankDepthReserve .localInverse M j := by
      unfold inverseBankDepthReserve inverseBankReserve
      exact mul_nonneg (mul_nonneg (by norm_num) (bankDepthFrame_pos M j).le) (Real.rpow_nonneg (by norm_num) _)
    have hrare := mul_nonneg heps (parent_weak_rare_trace_cap_nonneg M j)
    unfold parentWeakDirectionalBudget
    linarith only [hrare]
  have he (j omega) : f j omega=inverseHistoryDiscount^(2*j)*
      (lemmaVInverseDepthMax (originCube 2 n) (parentBoundaryBandFrameField M n height t omega) (r+j)*
        parentBoundaryBandCellTrace M n height t (originCube 2 n) (r+j) omega) := by
    dsimp only [f]
    rw [parent_boundary_band_inverse_depth]
    change _=inverseHistoryDiscount^(2*j)*
      (lemmaVInverseDepthMax (originCube 2 n) (parentBoundaryBandFrameField M n height t omega) (r+j)*
        parentBoundaryBandTraceDepth M n height t omega (r+j))
    ring
  have hef (j) : f j=(fun omega => inverseHistoryDiscount^(2*j)*
      (lemmaVInverseDepthMax (originCube 2 n) (parentBoundaryBandFrameField M n height t omega) (r+j)*
        parentBoundaryBandCellTrace M n height t (originCube 2 n) (r+j) omega)) := funext (he j)
  have hh := old_signed_nonnegative_series_integral (Cutoff.cutoffSampleLaw M).toMeasure f
    (fun j => 2*(inverseHistoryDiscount^(2*j)*parentWeakDirectionalBudget M n height U0 t j))
    (fun j => by rw [hef]; exact (hp j).1.const_mul _)
    (fun j omega => by
      dsimp only [f]
      apply mul_nonneg
      · exact mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
          (by rw [parent_boundary_band_inverse_depth]; exact lemmaVInverseDepthMax_nonneg _ _ _)
      · unfold parentBoundaryBandTraceDepth descendantsAverage
        exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
          (Finset.sum_nonneg (fun V _ => parent_boundary_band_trace_nonneg M n height t V omega)))
    hs (hbud.1.mul_left 2) (by
        intro j
        rw [hef]
        rw [integral_const_mul]
        exact (mul_le_mul_of_nonneg_left (hp j).2
          (pow_nonneg inverse_history_discount_range.1.le (2*j))).trans_eq (by ring))
  have hc : 0≤1-inverseHistoryDiscount^2 :=
    sub_nonneg.mpr (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  change Integrable (fun omega => (1-inverseHistoryDiscount^2)*∑' j,f j omega) _ ∧ _
  refine ⟨hh.1.const_mul _,?_⟩
  change (∫ omega,(1-inverseHistoryDiscount^2)*∑' j,f j omega ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤_
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hh.2 hc).trans_eq (by rw [tsum_mul_left]; ring)


/-- Actual-law weak return with the literal leading mean and a theta-scaled
reserve. The source depth is symbolic until its tiling is selected. -/
theorem parent_weak_actual_return
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hheight : 1 ≤ height) (hheight16 : height ≤ 16)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (depth : ℕ) (hdepth : depth=5) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    let W := parentBoundaryBandWeakProxy M n height depth t
    Integrable W (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,W ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        theta M*((23/100:ℝ)+t*parentBoundaryWeakMeanSlope gammaZero height+(1/10^12:ℝ)) := by
  intro W
  obtain ⟨U,hU⟩ := descendantsAtDepth_nonempty (originCube 2 n) depth
  have hw := parent_weak_actual_budget_payment M h hM hg n height hheight hheight16 depth hdepth U hU t ht hpast hstate
  have hb := parent_weak_directional_budget_return M h hM hg n height hheight hpast hstate depth hdepth U hU t ht
  exact ⟨hw.1,hw.2.trans ((mul_le_mul_of_nonneg_left hb.2 (by norm_num : (0:ℝ)≤2)).trans_eq (by ring))⟩

end
end ASDExplicitGamma.Native
