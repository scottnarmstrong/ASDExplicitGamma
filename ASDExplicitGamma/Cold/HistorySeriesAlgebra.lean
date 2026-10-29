module

public import ASDExplicitGamma.Cold.LpSeriesBound
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # The complete weighted history and its source tail split -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Literal complete weighted depth history. -/
def coldWeightedHistory (α : ℝ) (M : ℕ → ℝ) : ℝ :=
  (1-α)*(∑' r, α^r*M r)

/-- A monotone depth maximum is bounded by the complete history at the stated depth. -/
theorem cold_depth_le_weighted_history {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {M : ℕ → ℝ} (hM : ∀ r, 0 ≤ M r) (hmono : Monotone M)
    (hs : Summable (fun r => α^r*M r)) (r : ℕ) :
    α^r*M r ≤ coldWeightedHistory α M := by
  have hg : Summable (fun k : ℕ => α^(k+r)*M r) := by
    have h := (summable_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs,abs_of_pos hα]; exact hα1)).mul_right (α^r*M r)
    convert h using 1
    funext k
    rw [pow_add]
    ring
  have ht : Summable (fun k => α^(k+r)*M (k+r)) := (summable_nat_add_iff r).mpr hs
  have hbound := hg.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left
    (hmono (Nat.le_add_left r k)) (pow_nonneg hα.le _)) ht
  have heq : (∑' k : ℕ, α^(k+r)*M r) = α^r*M r/(1-α) := by
    have he : (fun k : ℕ => α^(k+r)*M r) = (fun k => α^k*(α^r*M r)) := by
      funext k; rw [pow_add]; ring
    rw [he,tsum_mul_right,tsum_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs,abs_of_pos hα]; exact hα1)]
    ring
  rw [heq] at hbound
  have hp := Finset.sum_nonneg (s := Finset.range r) (fun k _ => mul_nonneg (pow_nonneg hα.le k) (hM k))
  have hsplit := hs.sum_add_tsum_nat_add r
  have htotal : α^r*M r/(1-α) ≤ ∑' k, α^k*M k := by linarith only [hbound,hp,hsplit]
  have h := mul_le_mul_of_nonneg_left htotal (sub_nonneg.mpr hα1.le)
  rw [mul_div_cancel₀ _ (ne_of_gt (sub_pos.mpr hα1))] at h
  exact h

end ASDExplicitGamma.Cold
