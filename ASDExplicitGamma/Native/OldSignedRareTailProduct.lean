module

public import ASDExplicitGamma.Native.OldSignedBankRareHistory

/-! Exact positive binomial accounting for one additional inverse factor. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Inverse
noncomputable section

/-- Each non-leading bank tail is nonnegative on nonnegative data. -/
theorem old_signed_rare_tail_nonneg (b R X : ℝ) (hb : 0≤b) (hR : 0≤R) (hX : 0≤X) (k : ℕ) :
    0≤rareExpansionTail b R X k := by
  unfold rareExpansionTail
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hb _))
    (pow_nonneg hR _)) hX

/-- One extra bank factor is paid by the next positive binomial tail. -/
theorem old_signed_rare_tail_next (b R : ℝ) (hb : 0≤b) (hR : 0≤R) (k : ℕ) (hk : k≤3) :
    rareExpansionTail b R 1 k*(b+R)≤rareExpansionTail b R 1 (k+1) := by
  have h0 := old_signed_rare_power_binomial b R 1 k (by omega)
  have h1 := old_signed_rare_power_binomial b R 1 (k+1) (by omega)
  simp only [mul_one] at h0 h1
  have he : rareExpansionTail b R 1 (k+1)=
      rareExpansionTail b R 1 k*(b+R)+b^k*R := by
    rw [pow_succ,pow_succ,h0] at h1
    linarith only [h1]
  rw [he]
  exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg hb k) hR)

/-- The complete quarter-discounted tail factors without truncating the series. -/
theorem old_signed_quarter_rare_factor (b R : ℝ) (T : ℕ → ℝ) (k : ℕ) :
    (1-Scalar.inverseHistoryDiscount)*(∑' j : ℕ,Scalar.inverseHistoryDiscount^j*
      rareExpansionTail b R (T j) k)=rareExpansionTail b R 1 k*rawWeakTraceHistory T := by
  have he : (fun j : ℕ => Scalar.inverseHistoryDiscount^j*rareExpansionTail b R (T j) k)=
      (fun j : ℕ => rareExpansionTail b R 1 k*(Scalar.inverseHistoryDiscount^j*T j)) := by
    funext j
    rw [old_signed_rare_tail_linear b R (T j) k]
    ring
  rw [he,tsum_mul_left]
  unfold rawWeakTraceHistory
  ring

end
end ASDExplicitGamma.Native
