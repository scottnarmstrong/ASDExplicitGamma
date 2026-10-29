module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Positive series grouping before removing a correlated height selection. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open scoped ENNReal

/-- A selected slice of nonnegative errors is paid by the whole deterministic
series. Finite leading components keep their exact own sums. -/
theorem full_response_positive_series_selection
    {I J A B : Type*} [Fintype A] [Fintype B]
    (f : A → I → ℝ) (g : B → J → ℝ) (s : I → J) (hs : Function.Injective s)
    (hf0 : ∀ a i, 0 ≤ f a i) (hg0 : ∀ b j, 0 ≤ g b j)
    (hf : ∀ a, Summable (f a)) (hg : ∀ b, Summable (g b)) :
    (∑' i, ENNReal.ofReal ((∑ a, f a i)+(∑ b, g b (s i)))) ≤
      ENNReal.ofReal ((∑ a, ∑' i, f a i)+(∑ b, ∑' j, g b j)) := by
  have he (i : I) : ENNReal.ofReal ((∑ a, f a i)+(∑ b, g b (s i))) =
      (∑ a, ENNReal.ofReal (f a i))+(∑ b, ENNReal.ofReal (g b (s i))) := by
    rw [ENNReal.ofReal_add (Finset.sum_nonneg (fun a _ => hf0 a i))
      (Finset.sum_nonneg (fun b _ => hg0 b (s i))),
      ENNReal.ofReal_sum_of_nonneg (fun a _ => hf0 a i),
      ENNReal.ofReal_sum_of_nonneg (fun b _ => hg0 b (s i))]
  have hlead : (∑' i, ∑ a, ENNReal.ofReal (f a i)) =
      ∑ a, ENNReal.ofReal (∑' i, f a i) := by
    have hh : (∑' i, ∑ a, ENNReal.ofReal (f a i)) =
        ∑ a, ∑' i, ENNReal.ofReal (f a i) := by
      simpa only [tsum_fintype] using
        (ENNReal.tsum_comm (f := fun i a => ENNReal.ofReal (f a i)))
    rw [hh]
    apply Finset.sum_congr rfl
    intro a _
    exact (ENNReal.ofReal_tsum_of_nonneg (hf0 a) (hf a)).symm
  have herr : (∑' i, ∑ b, ENNReal.ofReal (g b (s i))) ≤
      ∑ b, ENNReal.ofReal (∑' j, g b j) := by
    have hh : (∑' i, ∑ b, ENNReal.ofReal (g b (s i))) =
        ∑ b, ∑' i, ENNReal.ofReal (g b (s i)) := by
      simpa only [tsum_fintype] using
        (ENNReal.tsum_comm (f := fun i b => ENNReal.ofReal (g b (s i))))
    rw [hh]
    apply Finset.sum_le_sum
    intro b _
    apply (ENNReal.tsum_comp_le_tsum_of_injective hs (fun j => ENNReal.ofReal (g b j))).trans_eq
    exact (ENNReal.ofReal_tsum_of_nonneg (hg0 b) (hg b)).symm
  simp_rw [he]
  rw [ENNReal.tsum_add,hlead]
  apply (add_le_add le_rfl herr).trans_eq
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => tsum_nonneg (hf0 a)),
    ← ENNReal.ofReal_sum_of_nonneg (fun b _ => tsum_nonneg (hg0 b)),
    ← ENNReal.ofReal_add (Finset.sum_nonneg (fun a _ => tsum_nonneg (hf0 a)))
      (Finset.sum_nonneg (fun b _ => tsum_nonneg (hg0 b)))]

end ASDExplicitGamma.Inverse
