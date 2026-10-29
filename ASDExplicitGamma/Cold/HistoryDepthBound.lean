module

public import ASDExplicitGamma.Cold.HistoryParameters
public import ASDExplicitGamma.Cold.HistorySeriesAlgebra

/-! # The actual complete history dominates each monotone depth maximum -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace ASDExplicitGamma.Cold

/-- The source inverse depth weight is exactly `3^(r/4)`. -/
theorem cold_history_inverse_weight (r : ℕ) :
    (coldHistoryAlpha^r)⁻¹ = (3:ℝ)^((r:ℝ)/4) := by
  dsimp [coldHistoryAlpha]
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3),← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3)]
  congr 1
  ring

/-- The complete history, rather than a truncation, gives the pathwise depth factor. -/
theorem cold_history_depth_bound {M : ℕ → ℝ} (hn : ∀ r, 0 ≤ M r) (hmono : Monotone M)
    (hs : Summable (fun r => coldHistoryAlpha^r*M r)) (r : ℕ) :
    M r ≤ (3:ℝ)^((r:ℝ)/4)*coldWeightedHistory coldHistoryAlpha M := by
  have h := cold_depth_le_weighted_history coldHistoryAlpha_pos coldHistoryAlpha_lt_one hn hmono hs r
  have hm := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (pow_nonneg coldHistoryAlpha_pos.le r))
  rw [← mul_assoc,inv_mul_cancel₀ (ne_of_gt (pow_pos coldHistoryAlpha_pos r)),one_mul,
    cold_history_inverse_weight] at hm
  exact hm

/-- The same depth bound holds almost everywhere for the actual L20-convergent history. -/
theorem cold_history_depth_bound_ae {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    {M : ℕ → Ω → ℝ} {b : ℕ → ℝ} (hM : ∀ r, MemLp (M r) 20 ℙ)
    (hb : Summable b) (hcap : ∀ r, lpNorm (fun ω => coldHistoryAlpha^r*M r ω) 20 ℙ ≤ b r)
    (hn : ∀ᵐ ω ∂ℙ, ∀ r, 0 ≤ M r ω) (hmono : ∀ᵐ ω ∂ℙ, Monotone (fun r => M r ω)) :
    ∀ᵐ ω ∂ℙ, ∀ r, M r ω ≤ (3:ℝ)^((r:ℝ)/4)*coldWeightedHistory coldHistoryAlpha (fun r => M r ω) := by
  have hs := cold_lpNorm_twenty_summable_ae (fun r => (hM r).const_mul (coldHistoryAlpha^r)) hb hcap
  filter_upwards [hs,hn,hmono] with ω hsω hnω hmω r
  have hseq : Summable (fun r => coldHistoryAlpha^r*M r ω) := by
    convert hsω using 1
    funext k
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg coldHistoryAlpha_pos.le k) (hnω k))]
  exact cold_history_depth_bound hnω hmω hseq r

end ASDExplicitGamma.Cold
