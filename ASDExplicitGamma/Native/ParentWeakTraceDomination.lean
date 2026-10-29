module

public import ASDExplicitGamma.Native.ParentWeakCoarseHistory
public import ASDExplicitGamma.Native.OldSignedWeakShiftBound
public import ASDExplicitGamma.Native.OldSignedMatrixHistoryControl
public import ASDExplicitGamma.Native.ParentBoundaryBandBankProxy

/-! Complete physical histories dominate each actual trace depth and the
shifted weak proxy. These losses are used only with rare remainders. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- Rational bounds for the actual quarter discount. -/
theorem parent_weak_discount_range :
    (1/2:ℝ) ≤ inverseHistoryDiscount ∧ inverseHistoryDiscount ≤ 9/10 := by
  have ha := inverse_history_discount_range.1.le
  have hh := old_signed_weak_discount_caps
  constructor <;> nlinarith only [ha,hh.1,hh.2]

/-- Each nonnegative trace average is controlled by the genuine complete
maximum history, without replacing the latter by a full response. -/
theorem parent_weak_trace_depth_le_history
    (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (j : ℕ) :
    descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1) ≤
      10*(inverseHistoryDiscount^j)⁻¹*oldSignedMaxTraceHistory Q a := by
  let T := descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)
  have hT0 : 0 ≤ T := descendantsAverage_nonneg Q j _ (fun U hU =>
    Cold.coarse_square_traceDefect_nonneg U
      (hEll.mono (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)))
  have hmax : T ≤ oldSignedMaxTraceDepth Q a j := by
    rw [←descendantsAverage_const Q j (oldSignedMaxTraceDepth Q a j)]
    apply descendantsAverage_le_descendantsAverage
    intro U hU
    exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨U,hU,rfl⟩
  have hs := old_signed_max_trace_series_summable Q a hEll
  have hterm := hs.le_tsum j (fun i _ => mul_nonneg
    (pow_nonneg inverse_history_discount_range.1.le _) (old_signed_max_trace_depth_bounds Q a hEll i).1)
  have hp := pow_pos inverse_history_discount_range.1 j
  have hpay : (1-inverseHistoryDiscount)*(inverseHistoryDiscount^j*T) ≤ oldSignedMaxTraceHistory Q a := by
    exact mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hmax hp.le).trans hterm)
      (sub_nonneg.mpr inverse_history_discount_range.2.le)
  have hten : (1:ℝ)≤10*(1-inverseHistoryDiscount) := by
    linarith only [parent_weak_discount_range.2]
  have hscaled : inverseHistoryDiscount^j*T ≤ 10*oldSignedMaxTraceHistory Q a := by
    calc
      _ = 1*(inverseHistoryDiscount^j*T) := (one_mul _).symm
      _ ≤ (10*(1-inverseHistoryDiscount))*(inverseHistoryDiscount^j*T) :=
        mul_le_mul_of_nonneg_right hten (mul_nonneg hp.le hT0)
      _ = 10*((1-inverseHistoryDiscount)*(inverseHistoryDiscount^j*T)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpay (by norm_num)
  have hh := mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hp.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul,mul_comm,mul_left_comm] using hh

/-- The complete shifted quarter trace is bounded by the same physical
maximum history. No new summability premise appears. -/
theorem parent_weak_shifted_trace_le_history
    (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (r : ℕ) :
    rawWeakTraceHistory (fun j => descendantsAverage Q (r+j)
      (fun U => traceDefect (openCubeSet U) a 1)) ≤
      (inverseHistoryDiscount^r)⁻¹*oldSignedMaxTraceHistory Q a := by
  let T := fun j => descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)
  have hT (j) : 0 ≤ T j := descendantsAverage_nonneg Q j _ (fun U hU =>
    Cold.coarse_square_traceDefect_nonneg U
      (hEll.mono (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)))
  have hshift := old_signed_weighted_shift_le inverseHistoryDiscount inverse_history_discount_range.1
    T hT (old_signed_trace_depth_series_summable Q a hEll) r
  have hsum := mul_le_mul_of_nonneg_left hshift (sub_nonneg.mpr inverse_history_discount_range.2.le)
  have hmax := old_signed_trace_history_le_max_trace Q a hEll
  have he : (1-inverseHistoryDiscount)*(∑' j : ℕ,inverseHistoryDiscount^j*T j)=
      (oldSignedTraceHistory Q a).toReal := by
    unfold oldSignedTraceHistory
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sub_nonneg.mpr inverse_history_discount_range.2.le),
      ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    change (1-inverseHistoryDiscount)*(∑' j : ℕ,inverseHistoryDiscount^j*T j)=
      (1-inverseHistoryDiscount)*(∑' j : ℕ,(ENNReal.ofReal (inverseHistoryDiscount^j*T j)).toReal)
    simp only [ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _) (hT _))]
  change (1-inverseHistoryDiscount)*(∑' j : ℕ,inverseHistoryDiscount^j*T (r+j)) ≤ _
  calc
    _ ≤ (1-inverseHistoryDiscount)*((inverseHistoryDiscount^r)⁻¹*(∑' j : ℕ,inverseHistoryDiscount^j*T j)) := hsum
    _ = (inverseHistoryDiscount^r)⁻¹*((1-inverseHistoryDiscount)*(∑' j : ℕ,inverseHistoryDiscount^j*T j)) := by ring
    _ = (inverseHistoryDiscount^r)⁻¹*(oldSignedTraceHistory Q a).toReal := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmax (inv_nonneg.mpr (pow_nonneg inverse_history_discount_range.1.le _))

end
end ASDExplicitGamma.Native
