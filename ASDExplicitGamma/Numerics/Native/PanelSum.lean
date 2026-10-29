module
public import ASDExplicitGamma.Numerics.Native.PanelIntegral
public import ASDExplicitGamma.Numerics.Native.PanelValues

/-! Closing a complete 512-panel certificate into its real integral bound. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics ASDExplicitGamma.Numerics.Mirror

theorem nativePanelCaps_sum (caps : List ℚ) :
    (∑ j ∈ Finset.range caps.length, (caps.getD j 0 : ℝ)) = (caps.sum : ℝ) := by
  induction caps with
  | nil => simp only [List.length_nil,Finset.range_zero,Finset.sum_empty,List.sum_nil,Rat.cast_zero]
  | cons c cs ih =>
    rw [List.length_cons,Finset.sum_range_succ']
    simp only [List.getD_cons_zero,List.getD_cons_succ,List.sum_cons,Rat.cast_add]
    rw [ih,add_comm]

theorem nativePanel_integral_caps (is : List QInterval) (rs : List ℝ) (caps : List ℚ)
    (hs : ∀ i, QInterval.Contains (is.getD i nativeZeroInterval) (rs.getD i 0))
    (hlen : is.length = rs.length) (hcaps : caps.length = 512)
    (hmono : MonotoneOn (nativePanelValue rs) (Set.Ici 0))
    (hcheck : nativePanelChecks is 0 caps = true) :
    (∫ s in (0 : ℝ)..1, nativePanelValue rs s) ≤ ((caps.sum/512 : ℚ) : ℝ) := by
  have hsums : (∑ j ∈ Finset.range 512, nativePanelValue rs (((j+1 : ℕ) : ℝ)/512)) ≤
      ∑ j ∈ Finset.range 512, (caps.getD j 0 : ℝ) := by
    apply Finset.sum_le_sum
    intro j hj
    have h := nativePanelChecks_sound is rs hs hlen 0 caps hcheck j
      (by rw [hcaps]; exact Finset.mem_range.mp hj)
    simpa only [Nat.zero_add,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] using h
  apply (native_integral_le_512_sum _ hmono).trans
  have h := div_le_div_of_nonneg_right hsums (by norm_num : (0 : ℝ) ≤ 512)
  have hc : (∑ j ∈ Finset.range 512, (caps.getD j 0 : ℝ)) = (caps.sum : ℝ) := by
    rw [← hcaps]
    exact nativePanelCaps_sum caps
  rw [hc] at h
  simpa only [Rat.cast_div,Rat.cast_ofNat] using h

end ASDExplicitGamma.Numerics.Native
