module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! The actual complete-mode passage for signed real feedback. Uniform
bounds for every finite subfamily prove summability before using real tsum. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- Uniform signed bounds for all finite subfamilies imply genuine real
summability and preserve the bound on the complete sum. -/
theorem old_signed_real_sum_of_finite_bound {I : Type*} (f : I → ℝ) (C : ℝ)
    (h : ∀ s : Finset I, |∑ n ∈ s,f n|≤C) :
    Summable f ∧ |∑' n,f n|≤C := by
  classical
  have hp (v : I → ℝ) (hv : ∀ s : Finset I, |∑ n ∈ s,v n|≤C) :
      Summable (fun n => if 0≤v n then v n else 0) := by
    apply summable_of_sum_le
    · intro n
      change 0≤(if 0≤v n then v n else 0)
      split_ifs with hn
      · exact hn
      · exact le_rfl
    · intro s
      have ht := (le_abs_self _).trans (hv (s.filter (fun n => 0≤v n)))
      simpa only [Finset.sum_filter] using ht
  have hpos := hp f h
  have hneg := hp (fun n => -f n) (by
    intro s
    simpa only [Finset.sum_neg_distrib,abs_neg] using h s)
  have he (n : I) : f n=(if 0≤f n then f n else 0)-(if 0≤ -f n then -f n else 0) := by
    split_ifs <;> linarith
  have hf : Summable f := (hpos.sub hneg).congr (fun n => (he n).symm)
  refine ⟨hf,abs_le.mpr ⟨?_,?_⟩⟩
  · have hn : (∑' n,-f n)≤C := hf.neg.tsum_le_of_sum_le (fun s => by
      rw [Finset.sum_neg_distrib]
      have ht := (abs_le.mp (h s)).1
      linarith)
    rw [tsum_neg] at hn
    linarith
  · exact hf.tsum_le_of_sum_le (fun s => (abs_le.mp (h s)).2)

end
end ASDExplicitGamma.Native
