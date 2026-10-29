module

public import ASDExplicitGamma.Triadic.HilbertHaarCoordinates
public import Mathlib.Topology.Algebra.Module.Basic

/-! Removing separability restrictions from Hilbert-valued field estimates. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open MeasureTheory TopologicalSpace

noncomputable section

/-- An orthonormal family in a separable Hilbert space is countable. -/
theorem hilbert_orthonormal_countable {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [SeparableSpace E] (b : ι → E) (hb : Orthonormal ℝ b) : Countable ι := by
  have hclose (i : ι) : ∃ n : ℕ, dist (b i) (denseSeq E n) < (1/4:ℝ) :=
    (denseRange_denseSeq E).exists_dist_lt (b i) (by norm_num)
  choose n hn using hclose
  apply Function.Injective.countable (f := n)
  intro i j hij
  by_contra hne
  have hdist : dist (b i) (b j) < 1/2 := by
    calc
      _ ≤ dist (b i) (denseSeq E (n i))+dist (denseSeq E (n i)) (b j) := dist_triangle _ _ _
      _ < 1/2 := by
        have hni := hn i
        rw [hij] at hni
        rw [hij, dist_comm (denseSeq E (n j)) (b j)]
        linarith only [hni, hn j]
  have hsq : dist (b i) (b j)^2 = 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, hb.norm_eq_one, hb.norm_eq_one, hb.inner_eq_zero hne]
    norm_num
  have hsqsmall := mul_self_lt_mul_self (dist_nonneg : 0 ≤ dist (b i) (b j)) hdist
  nlinarith only [hsq, hsqsmall]

/-- A strongly measurable field takes values almost everywhere in a closed
separable Hilbert subspace, even when its ambient Hilbert space is nonseparable. -/
theorem exists_separable_closed_subspace_ae {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure α} {F : α → E}
    (hF : AEStronglyMeasurable F μ) :
    ∃ V : Submodule ℝ E, IsClosed (V : Set E) ∧ IsSeparable (V : Set E) ∧ ∀ᵐ x ∂μ, F x ∈ V := by
  obtain ⟨s, hs, hmem⟩ := hF.isSeparable_ae_range
  let V := (Submodule.span ℝ s).topologicalClosure
  refine ⟨V, (Submodule.span ℝ s).isClosed_topologicalClosure, ?_, ?_⟩
  · change IsSeparable (closure (Submodule.span ℝ s : Set E))
    exact hs.span.closure
  · filter_upwards [hmem] with x hx
    exact (Submodule.span ℝ s).le_topologicalClosure (Submodule.subset_span hx)

end

end ASDExplicitGamma.Triadic
