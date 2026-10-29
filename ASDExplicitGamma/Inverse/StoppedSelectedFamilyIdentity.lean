module

public import ASDExplicitGamma.Inverse.StoppedSelectedBoundedFamily
public import ASDExplicitGamma.Inverse.StoppedSelectedDiscreteMoment

/-! Pointwise decomposition of a selected real family into its exact bounded and full tail parts. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
noncomputable section

/-- The complete real tail selector has exactly one nonzero atom. -/
theorem discrete_height_tail_sum_real {Ω : Type*} (H : Ω → ℕ) (Hs : ℕ)
    (c : ℕ → ℝ) (ω : Ω) :
    (if Hs < H ω then c (H ω-(Hs+1)) else 0) =
      ∑' n : ℕ, if H ω=Hs+1+n then c n else 0 := by
  classical
  by_cases hω : Hs < H ω
  · simp only [hω,ite_true]
    have hn : H ω=Hs+1+(H ω-(Hs+1)) := by omega
    symm
    rw [tsum_eq_single (H ω-(Hs+1))]
    · exact ite_eq_left hn
    · intro n hne
      have hn' : ¬H ω=Hs+1+n := by omega
      exact ite_eq_right hn'
  · simp only [hω,ite_false]
    symm
    have he : (fun n : ℕ => if H ω=Hs+1+n then c n else 0) = fun _ => 0 := by
      funext n
      exact ite_eq_right (by omega)
    rw [he,tsum_zero]

/-- Exact real selected-tail identity, including every unbounded height. -/
theorem selected_real_tail_eq {Ω : Type*} (H : Ω → ℕ) (Hs : ℕ) (f : ℕ → Ω → ℝ) (ω : Ω) :
    ({ω | Hs < H ω} : Set Ω).indicator (fun ω => f (H ω) ω) ω =
      ∑' n : ℕ, ({ω | H ω=Hs+1+n} : Set Ω).indicator (f (Hs+1+n)) ω := by
  have hh := discrete_height_tail_sum_real H Hs (fun n => f (Hs+1+n) ω) ω
  calc
    _ = (if Hs < H ω then f (Hs+1+(H ω-(Hs+1))) ω else 0) := by
      by_cases ht : Hs < H ω
      · simp only [Set.indicator,Set.mem_ofPred_eq,ht,ite_true]
        congr 1
        omega
      · simp only [Set.indicator,Set.mem_ofPred_eq,ht,ite_false]
    _ = _ := by
      apply hh.trans
      apply tsum_congr
      intro n
      simp only [Set.indicator,Set.mem_ofPred_eq]
      by_cases hn : H ω=Hs+1+n <;> simp only [hn,ite_true,ite_false]

/-- Exact selected-family partition into the twelve candidates and the full
tail. No relation between the family and the selection is assumed. -/
theorem selected_real_family_eq {Ω : Type*} (H : Ω → ℕ) (H0 : ℕ)
    (hH : ∀ ω, H0 ≤ H ω) (f : ℕ → Ω → ℝ) :
    (fun ω => f (H ω) ω) = selectedBoundedFamily H (selectedCandidateHeights H0) f+
      (fun ω => ∑' n : ℕ, ({ω | H ω=H0+12+n} : Set Ω).indicator (f (H0+12+n)) ω) := by
  funext ω
  simp only [Pi.add_apply]
  rw [selected_bounded_family_eq]
  have ht := selected_real_tail_eq H (H0+11) f ω
  change ({ω | H0+11 < H ω} : Set Ω).indicator (fun ω => f (H ω) ω) ω =
    ∑' n : ℕ, ({ω | H ω=H0+12+n} : Set Ω).indicator (f (H0+12+n)) ω at ht
  rw [← ht]
  by_cases hω : H ω ≤ H0+11
  · have hm : H ω ∈ selectedCandidateHeights H0 := (selected_candidate_mem H0 (H ω)).mpr ⟨hH ω,hω⟩
    rw [ite_eq_left hm,Set.indicator_of_notMem (by simpa only [Set.mem_ofPred_eq,not_lt] using hω)]
    exact (add_zero _).symm
  · have hm : H ω ∉ selectedCandidateHeights H0 := fun hm => hω ((selected_candidate_mem H0 (H ω)).mp hm).2
    rw [ite_eq_right hm,Set.indicator_of_mem (by simpa only [Set.mem_ofPred_eq] using lt_of_not_ge hω)]
    exact (zero_add _).symm

end
end ASDExplicitGamma.Inverse
