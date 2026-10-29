module

public import ASDExplicitGamma.Inverse.WhitneyRootTiles
public import Algsuperdiff.Section3.Provider.Whitney.LayerDensity

/-! Exact planar interior macro-cube counts underlying the corrected layer masses. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
open Algsuperdiff.Section3.Provider

/-- The non-boundary macro-cubes at a fixed depth in the source root. -/
noncomputable def interiorMacroCubes (l : ℤ) (k : ℕ) : Finset (TriadicCube 2) :=
  (descendantsAtDepth (originCube 2 l) k).filter (fun Q => ¬ Whitney.TouchesBoundary l Q)

/-- The actual descendant indices fill the complete integer box. -/
theorem descendant_indices (l : ℤ) (k : ℕ) :
    (descendantsAtDepth (originCube 2 l) k).image TriadicCube.index =
      Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-Whitney.extremeIdx k) (Whitney.extremeIdx k)) := by
  classical
  have hinj : Set.InjOn (TriadicCube.index (d := 2))
      (↑(descendantsAtDepth (originCube 2 l) k) : Set (TriadicCube 2)) := by
    intro Q hQ R hR he
    have hs := (scale_eq_sub_of_mem_descendantsAtDepth hQ).trans
      (scale_eq_sub_of_mem_descendantsAtDepth hR).symm
    cases Q
    cases R
    cases hs
    cases he
    rfl
  have hsub : (descendantsAtDepth (originCube 2 l) k).image TriadicCube.index ⊆
      Fintype.piFinset (fun _ : Fin 2 => Finset.Icc (-Whitney.extremeIdx k) (Whitney.extremeIdx k)) := by
    intro z hz
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hz
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    exact abs_le.mp (Whitney.abs_index_le_extremeIdx hQ i)
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_image_of_injOn hinj, descendantsAtDepth_card, Fintype.card_piFinset]
  simp only [Fin.prod_univ_two, Int.card_Icc]
  have he := Whitney.two_mul_extremeIdx_add_one k
  have he' : (Whitney.extremeIdx k + 1 - -Whitney.extremeIdx k).toNat = 3 ^ k := by
    have hp : ((3 : ℕ) ^ k : ℤ) = (3 : ℤ) ^ k := by push_cast; rfl
    have hE := Whitney.extremeIdx_nonneg k
    omega
  rw [he']
  norm_num only
  exact le_of_eq (by rw [← mul_pow]; norm_num)

/-- The non-boundary macro-cubes fill exactly the strictly interior index box. -/
theorem interior_macro_indices (l : ℤ) (k : ℕ) :
    (interiorMacroCubes l k).image TriadicCube.index =
      Fintype.piFinset (fun _ : Fin 2 =>
        Finset.Icc (-Whitney.extremeIdx k + 1) (Whitney.extremeIdx k - 1)) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hQd, hQn⟩ := Finset.mem_filter.mp hQ
    rw [Fintype.mem_piFinset]
    intro i
    have hi := Whitney.abs_index_le_extremeIdx_sub_one hQd hQn i
    rw [Finset.mem_Icc]
    constructor <;> linarith only [(abs_le.mp hi).1, (abs_le.mp hi).2]
  · intro hz
    have hb : z ∈ Fintype.piFinset (fun _ : Fin 2 =>
        Finset.Icc (-Whitney.extremeIdx k) (Whitney.extremeIdx k)) := by
      rw [Fintype.mem_piFinset] at hz ⊢
      intro i
      have hi := Finset.mem_Icc.mp (hz i)
      rw [Finset.mem_Icc]
      constructor <;> omega
    rw [← descendant_indices l k] at hb
    obtain ⟨Q, hQ, he⟩ := Finset.mem_image.mp hb
    refine Finset.mem_image.mpr ⟨Q, Finset.mem_filter.mpr ⟨hQ, ?_⟩, he⟩
    intro ht
    obtain ⟨i, hi⟩ := ht
    have hscale : Q.scale = l - (k : ℤ) := scale_eq_sub_of_mem_descendantsAtDepth hQ
    rw [hscale, Whitney.rootExtreme_sub_natCast, he] at hi
    have hz' := Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hz) i)
    rcases hi with hi | hi <;> omega

/-- Exact planar count of strictly interior macro-cubes at depth k. -/
theorem interior_macro_card (l : ℤ) (k : ℕ) :
    (interiorMacroCubes l k).card = (3 ^ k - 2) ^ 2 := by
  classical
  have hinj : Set.InjOn (TriadicCube.index (d := 2))
      (↑(interiorMacroCubes l k) : Set (TriadicCube 2)) := by
    intro Q hQ R hR he
    have hs := (scale_eq_sub_of_mem_descendantsAtDepth (Finset.mem_filter.mp hQ).1).trans
      (scale_eq_sub_of_mem_descendantsAtDepth (Finset.mem_filter.mp hR).1).symm
    cases Q
    cases R
    cases hs
    cases he
    rfl
  rw [← Finset.card_image_of_injOn hinj, interior_macro_indices, Fintype.card_piFinset]
  simp only [Fin.prod_univ_two, Int.card_Icc]
  have he := Whitney.two_mul_extremeIdx_add_one k
  have he' : (Whitney.extremeIdx k - 1 + 1 - (-Whitney.extremeIdx k + 1)).toNat =
      3 ^ k - 2 := by
    have hp : ((3 : ℕ) ^ k : ℤ) = (3 : ℤ) ^ k := by push_cast; rfl
    have hE := Whitney.extremeIdx_nonneg k
    omega
  rw [he']
  ring

end ASDExplicitGamma.Inverse
