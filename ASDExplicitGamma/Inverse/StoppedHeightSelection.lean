module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Data.Nat.Find
public import Mathlib.Tactic.ByContra

/-! The literal source stopped height: the first level after the last failed separation. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
noncomputable section

/-- All separations at and above n are successful, respecting the fixed entrance. -/
def HeightGood {Ω : Type*} (H0 : ℕ) (E : ℕ → Set Ω) (ω : Ω) (n : ℕ) : Prop :=
  H0 ≤ n ∧ ∀ k, n ≤ k → ω ∉ E k

/-- A sample has only finitely many failed separations above the entrance. -/
def HeightSuccessful {Ω : Type*} (H0 : ℕ) (E : ℕ → Set Ω) (ω : Ω) : Prop :=
  ∃ n, HeightGood H0 E ω n

/-- A total defining predicate: on the exceptional samples without a last
failure it returns the entrance, and elsewhere the exact first good height. -/
def HeightTotalGood {Ω : Type*} (H0 : ℕ) (E : ℕ → Set Ω) (ω : Ω) (n : ℕ) : Prop :=
  HeightGood H0 E ω n ∨ (n=H0 ∧ ¬ HeightSuccessful H0 E ω)

theorem height_total_exists {Ω : Type*} (H0 : ℕ) (E : ℕ → Set Ω) (ω : Ω) :
    ∃ n, HeightTotalGood H0 E ω n := by
  classical
  by_cases hs : HeightSuccessful H0 E ω
  · obtain ⟨n,hn⟩ := hs
    exact ⟨n,Or.inl hn⟩
  · exact ⟨H0,Or.inr ⟨rfl,hs⟩⟩

/-- The source height max(H0,1+last failed separation), with a stated total
convention on the null exceptional set where there is no last failure. -/
def stoppedHeight {Ω : Type*} (H0 : ℕ) (E : ℕ → Set Ω) (ω : Ω) : ℕ := by
  classical
  exact Nat.find (height_total_exists H0 E ω)

/-- The height is always at least its fixed source entrance. -/
theorem stopped_height_ge {Ω : Type*} (H0 : ℕ) (E : ℕ → Set Ω) (ω : Ω) :
    H0 ≤ stoppedHeight H0 E ω := by
  classical
  have hs := Nat.find_spec (height_total_exists H0 E ω)
  change HeightTotalGood H0 E ω (stoppedHeight H0 E ω) at hs
  rcases hs with hgood | ⟨he,_⟩
  · exact hgood.1
  · exact he.ge

/-- On every sample with a successful cutoff, all later separations really
succeed. No probabilistic or measurability conclusion is assumed here. -/
theorem stopped_height_good {Ω : Type*} (H0 : ℕ) (E : ℕ → Set Ω) (ω : Ω)
    (hω : HeightSuccessful H0 E ω) : HeightGood H0 E ω (stoppedHeight H0 E ω) := by
  classical
  have hs := Nat.find_spec (height_total_exists H0 E ω)
  change HeightTotalGood H0 E ω (stoppedHeight H0 E ω) at hs
  rcases hs with hgood | ⟨_,hbad⟩
  · exact hgood
  · exact False.elim (hbad hω)

/-- A selected height above h forces a real failure at some k>=h. -/
theorem stopped_height_tail_subset {Ω : Type*} (H0 : ℕ) (E : ℕ → Set Ω) (h : ℕ) (hh : H0 ≤ h) :
    {ω | h < stoppedHeight H0 E ω} ⊆ ⋃ k : ℕ, ⋃ _hk : h ≤ k, E k := by
  classical
  intro ω hω
  by_contra! hn
  have hall : ∀ k, h ≤ k → ω ∉ E k := by
    intro k hk hE
    exact hn (Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hk,hE⟩⟩)
  have hbound := Nat.find_min' (height_total_exists H0 E ω) (Or.inl ⟨hh,hall⟩)
  change stoppedHeight H0 E ω ≤ h at hbound
  exact Nat.not_lt_of_ge hbound hω

/-- The successful cutoff event is genuinely measurable from the actual
separation events, including the entire countable future. -/
theorem height_good_measurable {Ω : Type*} [MeasurableSpace Ω] (H0 : ℕ) (E : ℕ → Set Ω)
    (hE : ∀ n, MeasurableSet (E n)) (n : ℕ) : MeasurableSet {ω | HeightGood H0 E ω n} := by
  by_cases hn : H0 ≤ n
  · simp only [HeightGood,hn,true_and]
    have he : {ω | ∀ k, n ≤ k → ω ∉ E k} = ⋂ k : ℕ, ⋂ _hk : n ≤ k, (E k)ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq,Set.mem_iInter,Set.mem_compl_iff]
    rw [he]
    exact MeasurableSet.iInter (fun k : ℕ => MeasurableSet.iInter (fun _hk : n ≤ k => (hE k).compl))
  · simp only [HeightGood,hn,false_and,Set.ofPred_false]
    exact MeasurableSet.empty

/-- The selected height is an ordinary measurable natural-valued random variable. -/
theorem stopped_height_measurable {Ω : Type*} [MeasurableSpace Ω] (H0 : ℕ) (E : ℕ → Set Ω)
    (hE : ∀ n, MeasurableSet (E n)) : Measurable (stoppedHeight H0 E) := by
  classical
  have hs : MeasurableSet {ω | HeightSuccessful H0 E ω} := by
    simpa only [HeightSuccessful,Set.iUnion_ofPred] using
      MeasurableSet.iUnion (fun n => height_good_measurable H0 E hE n)
  apply measurable_find (height_total_exists H0 E)
  intro n
  by_cases hn : n = H0
  · simp only [HeightTotalGood,hn,true_and]
    exact (height_good_measurable H0 E hE H0).union hs.compl
  · simp only [HeightTotalGood,hn,false_and,or_false]
    exact height_good_measurable H0 E hE n

end
end ASDExplicitGamma.Inverse
