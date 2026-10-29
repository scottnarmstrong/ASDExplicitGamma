module

public import ASDExplicitGamma.Inverse.WhitneyInteriorCount

/-! The exact newly finalized macro-cubes in each planar Whitney layer. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
open Algsuperdiff.Section3.Provider

/-- Macro-layer n+1 consists of the non-boundary children of boundary parents
at depth n, exactly as in the source's recursive partition. -/
noncomputable def newMacroCubes (l : ℤ) (n : ℕ) : Finset (TriadicCube 2) :=
  ((descendantsAtDepth (originCube 2 l) n).filter (Whitney.TouchesBoundary l)).biUnion
    (fun A => (childCubes A).filter (fun C => ¬ Whitney.TouchesBoundary l C))

/-- Interior macro-cubes at the next depth split into newly finalized cubes
and all children of the previously interior cubes. -/
theorem interior_next_partition (l : ℤ) (n : ℕ) :
    interiorMacroCubes l (n + 1) = newMacroCubes l n ∪
      (interiorMacroCubes l n).biUnion childCubes := by
  classical
  ext C
  constructor
  · intro hC
    obtain ⟨hCd, hCn⟩ := Finset.mem_filter.mp hC
    obtain ⟨A, hA, hCA⟩ := mem_descendantsAtDepth_succ_iff.mp hCd
    by_cases ht : Whitney.TouchesBoundary l A
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨A, Finset.mem_filter.mpr ⟨hA, ht⟩, Finset.mem_filter.mpr ⟨hCA, hCn⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨A, Finset.mem_filter.mpr ⟨hA, ht⟩, hCA⟩)
  · intro hC
    rcases Finset.mem_union.mp hC with hC | hC
    · obtain ⟨A, hA, hCA⟩ := Finset.mem_biUnion.mp hC
      exact Finset.mem_filter.mpr ⟨mem_descendantsAtDepth_succ_iff.mpr
        ⟨A, (Finset.mem_filter.mp hA).1, (Finset.mem_filter.mp hCA).1⟩,
        (Finset.mem_filter.mp hCA).2⟩
    · obtain ⟨A, hA, hCA⟩ := Finset.mem_biUnion.mp hC
      obtain ⟨hAd, hAn⟩ := Finset.mem_filter.mp hA
      refine Finset.mem_filter.mpr ⟨mem_descendantsAtDepth_succ_iff.mpr ⟨A, hAd, hCA⟩, ?_⟩
      intro ht
      exact hAn (Whitney.touchesBoundary_parent_of_child
        (scale_eq_sub_of_mem_descendantsAtDepth hAd) hCA ht)

/-- The two parts of the next-depth interior partition are disjoint. -/
theorem interior_next_disjoint (l : ℤ) (n : ℕ) :
    Disjoint (newMacroCubes l n) ((interiorMacroCubes l n).biUnion childCubes) := by
  classical
  apply Finset.disjoint_left.mpr
  intro C hC hC'
  obtain ⟨A, hA, hCA⟩ := Finset.mem_biUnion.mp hC
  obtain ⟨B, hB, hCB⟩ := Finset.mem_biUnion.mp hC'
  have hab : A = B := by
    by_contra hn
    exact Finset.disjoint_left.mp (disjoint_childCubes_of_ne hn)
      (Finset.mem_filter.mp hCA).1 hCB
  exact (Finset.mem_filter.mp hB).2 (hab ▸ (Finset.mem_filter.mp hA).2)

/-- Exact macro-layer accounting: nine old interior children and the newly
finalized layer make precisely the next interior box. -/
theorem new_macro_card_identity (l : ℤ) (n : ℕ) :
    (newMacroCubes l n).card + 9 * (interiorMacroCubes l n).card =
      (interiorMacroCubes l (n + 1)).card := by
  classical
  rw [interior_next_partition, Finset.card_union_of_disjoint (interior_next_disjoint l n)]
  congr 1
  rw [Finset.card_biUnion]
  · simp only [childCubes_card, Finset.sum_const, nsmul_eq_mul]
    norm_num
    omega
  · intro A hA B hB hAB
    exact disjoint_childCubes_of_ne hAB

/-- The first finalized macro-layer is the unique central third-square. -/
theorem new_macro_card_zero (l : ℤ) : (newMacroCubes l 0).card = 1 := by
  have h := new_macro_card_identity l 0
  rw [interior_macro_card, interior_macro_card] at h
  norm_num at h
  exact h

/-- Exact real macro-layer count for every later layer. -/
theorem new_macro_card (l : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    ((newMacroCubes l n).card : ℝ) = 8 * (3 : ℝ) ^ (n + 1) - 32 := by
  have hp : 2 ≤ (3 : ℕ) ^ n := by
    cases n with
    | zero => omega
    | succ k =>
      rw [pow_succ]
      have hh : 0 < (3 : ℕ) ^ k := pow_pos (by decide) _
      omega
  have hp1 : 2 ≤ (3 : ℕ) ^ (n + 1) := by
    rw [pow_succ]
    omega
  have h := new_macro_card_identity l n
  rw [interior_macro_card, interior_macro_card] at h
  have hc := congrArg (fun a : ℕ => (a : ℝ)) h
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_sub hp, Nat.cast_sub hp1] at hc
  rw [pow_succ (3 : ℝ) n] at hc ⊢
  nlinarith only [hc]

/-- Fine source layers are exactly all profile-depth descendants of the
newly finalized macro-layer. -/
theorem whitney_layer_eq_macro_descendants (l : ℤ) (H n : ℕ) :
    bankWhitneyLayer l H (n + 1) =
      (newMacroCubes l n).biUnion (fun C => descendantsAtDepth C (whitneyProfile H (n + 1))) := by
  classical
  unfold bankWhitneyLayer Whitney.whitneyLayer newMacroCubes
  rw [ite_eq_left (by omega : 1 ≤ n + 1), Nat.add_sub_cancel, Finset.biUnion_biUnion]

end ASDExplicitGamma.Inverse
