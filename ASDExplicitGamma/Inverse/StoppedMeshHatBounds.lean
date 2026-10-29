module

public import ASDExplicitGamma.Triadic.DiagSobolev
public import Mathlib.Data.Int.Interval

/-! Sharp one-dimensional mesh-hat payments for the planar compatible
midpoint gradient. These retain the factor two, rather than paying every node. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization ASDExplicitGamma.Triadic
noncomputable section

theorem diag_hat_positive_support {t : ℝ} (ht : diagHat t ≠ 0) : -1 < t ∧ t < 1 := by
  have hpos : 0 < diagHat t := lt_of_le_of_ne (diagHat_nonneg t) ht.symm
  have hab : |t| < 1 := by
    unfold diagHat at hpos
    exact sub_pos.mp ((lt_max_iff.mp hpos).resolve_left (by simp))
  exact abs_lt.mp hab

theorem mesh_integer_window {s : ℝ} {k : ℤ} (hlo : s-1 ≤ k) (hhi : (k:ℝ) < s+1) :
    k ∈ Finset.Icc (⌈s⌉-1) ⌈s⌉ := by
  have hc := Int.ceil_lt_add_one s
  have hs := Int.le_ceil s
  have h1 : (⌈s⌉:ℝ)-2 < k := by linarith only [hc,hlo]
  have h2 : (k:ℝ) < (⌈s⌉:ℝ)+1 := by linarith only [hs,hhi]
  have h1Z : ⌈s⌉-2 < k := by exact_mod_cast h1
  have h2Z : k < ⌈s⌉+1 := by exact_mod_cast h2
  exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩

theorem diag_hat_pair_sum (s : ℝ) (k : ℤ) :
    diagHat (s-k)+diagHat (s-(k+1:ℤ)) ≤ 1 := by
  by_cases h0 : diagHat (s-k) = 0
  · rw [h0,zero_add]
    exact diagHat_le_one _
  by_cases h1 : diagHat (s-(k+1:ℤ)) = 0
  · rw [h1,add_zero]
    exact diagHat_le_one _
  have hx := diag_hat_positive_support h0
  have hy := diag_hat_positive_support h1
  have ha := abs_sub_le (s-(k:ℝ)) 0 (s-((k+1:ℤ):ℝ))
  norm_num only [Int.cast_add,Int.cast_one,sub_zero,zero_sub,abs_neg] at ha hy ⊢
  have hd : |(s-(k:ℝ))-(s-((k:ℝ)+1))| = 1 := by
    rw [show (s-(k:ℝ))-(s-((k:ℝ)+1)) = 1 by ring,abs_one]
  rw [hd] at ha
  have hax : |s-(k:ℝ)| ≤ 1 := (abs_lt.mpr hx).le
  have hay : |s-((k:ℝ)+1)| ≤ 1 := (abs_lt.mpr hy).le
  rw [diagHat,max_eq_right (sub_nonneg.mpr hax),diagHat,max_eq_right (sub_nonneg.mpr hay)]
  linarith only [ha]

/-- Any finite set of integer mesh hats has total mass at most one. -/
theorem diag_hat_mesh_sum (S : Finset ℤ) (s : ℝ) :
    (∑ k ∈ S, diagHat (s-k)) ≤ 1 := by
  classical
  let T := S.filter (fun k : ℤ => diagHat (s-k) ≠ 0)
  have he : (∑ k ∈ S, diagHat (s-k)) = ∑ k ∈ T, diagHat (s-k) := by
    apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro k hk hkn
    simpa only [T,Finset.mem_filter,hk,true_and,not_not] using hkn
  have hsub : T ⊆ Finset.Icc (⌈s⌉-1) ⌈s⌉ := by
    intro k hk
    have hp := diag_hat_positive_support (Finset.mem_filter.mp hk).2
    exact mesh_integer_window (by linarith only [hp.2]) (by linarith only [hp.1])
  rw [he]
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => diagHat_nonneg _)).trans
  have hi : Finset.Icc (⌈s⌉-1) ⌈s⌉ = {⌈s⌉-1,⌈s⌉} := by
    simpa only [sub_add_cancel] using (Int.Icc_eq_pair (a := ⌈s⌉-1))
  rw [hi,Finset.sum_pair (by omega : ⌈s⌉-1 ≠ ⌈s⌉)]
  simpa only [sub_add_cancel] using (diag_hat_pair_sum s (⌈s⌉-1))

end
end ASDExplicitGamma.Inverse
