module

public import ASDExplicitGamma.Inverse.StoppedTwoGroupSupport

/-! The whole-root H1 midpoint correction equals the two actually active
source groups in every Whitney interior, on one common spatial null set. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- The two possible canonical groups are n and n-1. -/
theorem two_group_hasSum (f : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hfar : ∀ a, a ≠ n → a+1 ≠ n → f a=0) : HasSum f (f n+f (n-1)) := by
  have hh := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) (s := ({n,n-1} : Finset ℕ)) (f := f)
    (fun a ha => hfar a (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at ha; exact ha.1)
      (by simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at ha; omega))
  simpa only [Finset.sum_pair (by omega : n ≠ n-1)] using hh

variable (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
  (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
  (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
    (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
  (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
  (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)

end
end ASDExplicitGamma.Inverse
