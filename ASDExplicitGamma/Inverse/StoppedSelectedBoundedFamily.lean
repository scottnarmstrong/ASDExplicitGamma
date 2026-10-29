module

public import ASDExplicitGamma.Inverse.StoppedSelectedMaximum
public import ASDExplicitGamma.Inverse.StoppedSelectedCandidates

/-! Finite selected wave families pay exactly twelve candidates, without independence. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The actual selected observable restricted to a finite candidate set. -/
def selectedBoundedFamily {Ω : Type*} (H : Ω → ℕ) (s : Finset ℕ)
    (f : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ k ∈ s, ({ω | H ω=k} : Set Ω).indicator (f k) ω

/-- The finite atomic sum is exactly the selected value on the candidate set. -/
theorem selected_bounded_family_eq {Ω : Type*} (H : Ω → ℕ) (s : Finset ℕ)
    (f : ℕ → Ω → ℝ) (ω : Ω) :
    selectedBoundedFamily H s f ω = if H ω ∈ s then f (H ω) ω else 0 := by
  classical
  unfold selectedBoundedFamily
  by_cases hω : H ω ∈ s
  · rw [ite_eq_left hω,Finset.sum_eq_single (H ω)]
    · have hm : ω ∈ {ω | H ω=H ω} := rfl
      exact Set.indicator_of_mem hm (f (H ω))
    · intro k _ hne
      have hn : ω ∉ {ω | H ω=k} := by
        intro he
        change H ω=k at he
        exact hne he.symm
      exact Set.indicator_of_notMem hn (f k)
    · exact fun h => False.elim (h hω)
  · rw [ite_eq_right hω]
    apply Finset.sum_eq_zero
    intro k hk
    have hn : ω ∉ {ω | H ω=k} := by
      intro he
      change H ω=k at he
      exact hω (he.symm ▸ hk)
    exact Set.indicator_of_notMem hn (f k)

/-- Arbitrary dependence of the selection and the candidates still costs
only card(s)^(1/p), rather than card(s). -/
theorem selected_bounded_family_Lp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : Ω → ℕ) (hH : Measurable H) (s : Finset ℕ)
    (f : ℕ → Ω → ℝ) (hf : ∀ k, Measurable (f k)) (p : ℝ) (hp : 0 < p)
    (B : ℝ≥0∞) (hB : ∀ k ∈ s, eLpNorm (f k) (ENNReal.ofReal p) μ ≤ B) :
    eLpNorm (selectedBoundedFamily H s f) (ENNReal.ofReal p) μ ≤ (s.card:ℝ≥0∞)^(1/p:ℝ)*B := by
  have hE (k : ℕ) : MeasurableSet {ω | H ω=k} := hH (measurableSet_singleton _)
  have hm : Measurable (selectedBoundedFamily H s f) :=
    Finset.measurable_sum _ (fun k _ => (hf k).indicator (hE k))
  have hmax := finite_maximum_Lp μ s (fun k ω => ‖f k ω‖ₑ) (fun k => (hf k).enorm) p hp B
    (fun k hk => by rw [eLpNorm_enorm _ (hf k).aestronglyMeasurable]; exact hB k hk)
  apply le_trans _ hmax
  apply eLpNorm_mono_enorm hm.aestronglyMeasurable
  intro ω
  rw [selected_bounded_family_eq,enorm_eq_self]
  by_cases hω : H ω ∈ s
  · rw [ite_eq_left hω]
    exact Finset.le_sup (f := fun k => ‖f k ω‖ₑ) hω
  · rw [ite_eq_right hω,enorm_zero]
    exact zero_le

/-- The exact twelve-candidate source factor for both fixed tuples. -/
theorem selected_twelve_candidate_Lp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : Ω → ℕ) (hH : Measurable H) (H0 : ℕ)
    (f : ℕ → Ω → ℝ) (hf : ∀ k, Measurable (f k)) (p : ℝ) (hp : 0 < p)
    (B : ℝ≥0∞) (hB : ∀ k ∈ selectedCandidateHeights H0, eLpNorm (f k) (ENNReal.ofReal p) μ ≤ B) :
    eLpNorm (selectedBoundedFamily H (selectedCandidateHeights H0) f) (ENNReal.ofReal p) μ ≤
      (12:ℝ≥0∞)^(1/p:ℝ)*B := by
  simpa only [selected_candidate_heights_card,Nat.cast_ofNat] using
    selected_bounded_family_Lp μ H hH (selectedCandidateHeights H0) f hf p hp B hB

end
end ASDExplicitGamma.Inverse
