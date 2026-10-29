module

public import ASDExplicitGamma.Native.OldSignedShiftedTraceProxy
public import ASDExplicitGamma.Native.OldSignedWeightedMeanRatios

/-! A coarse complete-history majorant used only for rare bank products. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse
noncomputable section

/-- A shifted nonnegative geometric series is controlled by the complete
series. This loss is used only in the rare reserve, never in the leading term. -/
theorem old_signed_weighted_shift_le (w : ℝ) (hw : 0<w) (f : ℕ → ℝ)
    (hf : ∀ j,0≤f j) (hs : Summable (fun j => w^j*f j)) (r : ℕ) :
    (∑' j : ℕ,w^j*f (r+j))≤(w^r)⁻¹*(∑' j : ℕ,w^j*f j) := by
  have htail := hs.sum_add_tsum_nat_add r
  have hp : 0≤∑ j ∈ Finset.range r,w^j*f j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (pow_nonneg hw.le _) (hf j))
  have ht : (∑' j : ℕ,w^(j+r)*f (j+r))≤∑' j : ℕ,w^j*f j := by linarith only [htail,hp]
  have he : (∑' j : ℕ,w^(j+r)*f (j+r))=w^r*(∑' j : ℕ,w^j*f (r+j)) := by
    rw [←tsum_mul_left]
    apply tsum_congr
    intro j
    rw [pow_add,Nat.add_comm j r]
    ring
  rw [he] at ht
  have hh := mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr (pow_nonneg hw.le r))
  simpa only [←mul_assoc,inv_mul_cancel₀ (pow_ne_zero r hw.ne'),one_mul] using hh

/-- The actual shifted proxy is bounded by the full parent proxy. -/
theorem old_signed_shifted_weak_proxy_le (Q : TriadicCube 2) (r : ℕ) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q a (r+j))
      (fun j => descendantsAverage Q (r+j) (fun U => traceDefect (openCubeSet U) a 1))≤
    (inverseHistoryDiscount^(2*r))⁻¹*
      rawWeakTraceProxy (lemmaVInverseDepthMax Q a)
        (fun j => descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)) := by
  let f := fun j => lemmaVInverseDepthMax Q a j*
    descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)
  have hs := old_signed_weak_trace_proxy_summable Q a hEll
  have hs' : Summable (fun j => (inverseHistoryDiscount^2)^j*f j) := by
    simpa only [f,pow_mul,mul_assoc] using hs
  have hn (j : ℕ) : 0≤f j := mul_nonneg (lemmaVInverseDepthMax_nonneg Q a j)
    (descendantsAverage_nonneg Q j _ (fun U hU => Cold.coarse_square_traceDefect_nonneg U
      (hEll.mono (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU))))
  have hh := old_signed_weighted_shift_le (inverseHistoryDiscount^2)
    (pow_pos inverse_history_discount_range.1 _) f hn hs' r
  have hw : 0≤1-inverseHistoryDiscount^2 := sub_nonneg.mpr
    (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  have hscaled := mul_le_mul_of_nonneg_left hh hw
  simpa only [rawWeakTraceProxy,f,pow_mul,mul_assoc,mul_left_comm] using hscaled

/-- The depth-five rare loss, including D, is at most thirty-two. -/
theorem old_signed_q1_rare_shift_factor :
    (inverseHistoryDiscount^(2*5))⁻¹*(1+inverseHistoryDiscount)≤32 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤577/1000) old_signed_weak_discount_caps.1 5
  have hlo : (1/16:ℝ)≤ inverseHistoryDiscount^(2*5) := by
    rw [pow_mul]
    exact (by norm_num : (1/16:ℝ)≤(577/1000)^5).trans hp
  have hi : (inverseHistoryDiscount^(2*5))⁻¹≤16 := by
    calc
      _ ≤ (1/16:ℝ)⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/16) hlo
      _ = _ := by norm_num
  have hd : 1+inverseHistoryDiscount≤2 := by linarith only [inverse_history_discount_range.2]
  exact (mul_le_mul hi hd (add_nonneg (by norm_num) inverse_history_discount_range.1.le) (by norm_num)).trans_eq (by norm_num)

end
end ASDExplicitGamma.Native
