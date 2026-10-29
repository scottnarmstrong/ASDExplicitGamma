module

public import Mathlib.Probability.BorelCantelli
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-! # Centered independent Hilbert sums and their nonnegative norm submartingale -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

section
variable {Ω E : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- Finite sums of centered independent increments form a martingale in their natural filtration. -/
theorem independent_sum_martingale (X : ℕ → Ω → E) (hX : ∀ n, StronglyMeasurable (X n))
    (hind : iIndepFun X μ) (hint : ∀ n, Integrable (X n) μ) (hmean : ∀ n, ∫ ω, X n ω ∂μ = 0) :
    Martingale (fun n ω => ∑ j ∈ Finset.range (n + 1), X j ω) (Filtration.natural X hX) μ := by
  let ℱ := Filtration.natural X hX
  have had : StronglyAdapted ℱ (fun n ω => ∑ j ∈ Finset.range (n + 1), X j ω) := by
    intro n
    have hs : StronglyMeasurable[ℱ n] (∑ j ∈ Finset.range (n + 1), X j) := by
      apply Finset.stronglyMeasurable_sum
      intro j hj
      have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
      exact ((Filtration.stronglyAdapted_natural hX) j).mono (ℱ.mono hjn)
    convert hs using 1
    ext ω
    simp only [Finset.sum_apply]
  have hi (n : ℕ) : Integrable (fun ω => ∑ j ∈ Finset.range (n + 1), X j ω) μ :=
    integrable_finsetSum _ (fun j _ => hint j)
  apply martingale_of_condExp_sub_eq_zero_nat had hi
  intro n
  have he : (fun ω => ∑ j ∈ Finset.range (n + 1 + 1), X j ω) -
      (fun ω => ∑ j ∈ Finset.range (n + 1), X j ω) = X (n + 1) := by
    funext ω
    simp only [Pi.sub_apply, Finset.sum_range_succ, add_sub_cancel_left]
  rw [he]
  have hh := hind.condExp_natural_ae_eq_of_lt hX (Nat.lt_succ_self n)
  filter_upwards [hh] with ω hω
  exact hω.trans (hmean (n + 1))

omit [IsProbabilityMeasure μ] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] in
/-- Conditional Jensen gives the nonnegative norm submartingale, retaining the same filtration. -/
theorem martingale_norm_submartingale {ℱ : Filtration ℕ m} (S : ℕ → Ω → E)
    (hS : Martingale S ℱ μ) (hint : ∀ n, Integrable (S n) μ) :
    Submartingale (fun n ω => ‖S n ω‖) ℱ μ := by
  refine ⟨fun n => continuous_norm.comp_stronglyMeasurable (hS.1 n), ?_, fun n => (hint n).norm⟩
  intro i j hij
  filter_upwards [hS.2 i j hij, norm_condExp_le (m := ℱ i) (S j)] with ω he hn
  rw [he] at hn
  exact hn

end
end ASDExplicitGamma.Gaussian
