module

public import ASDExplicitGamma.Inverse.ContainedTriangleCubes
public import Mathlib.Data.Finset.Prod

/-! Exact count of contained cubes from ordered coordinate bins. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
open Algsuperdiff.Section3.Provider

/-- The actual contained cubes correspond exactly to strictly ordered pairs
of depth-n coordinate bins. -/
theorem triangle_contained_pairs (l : ℤ) (pi : Equiv.Perm (Fin 2)) (n : ℕ) :
    (triangleContainedCubes l pi n).image (fun R => (R.index (pi 0), R.index (pi 1))) =
      ((Finset.Icc (-Whitney.extremeIdx n) (Whitney.extremeIdx n)) ×ˢ
        (Finset.Icc (-Whitney.extremeIdx n) (Whitney.extremeIdx n))).filter
          (fun p => p.1 < p.2) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hRd, hRo⟩ := Finset.mem_filter.mp hR
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr (abs_le.mp (Whitney.abs_index_le_extremeIdx hRd (pi 0))),
       Finset.mem_Icc.mpr (abs_le.mp (Whitney.abs_index_le_extremeIdx hRd (pi 1)))⟩, hRo⟩
  · intro hp
    obtain ⟨hbox, hlt⟩ := Finset.mem_filter.mp hp
    obtain ⟨h0, h1⟩ := Finset.mem_product.mp hbox
    let z : Fin 2 → ℤ := fun i => if pi.symm i = 0 then p.1 else p.2
    have hz : z ∈ Fintype.piFinset (fun _ : Fin 2 =>
        Finset.Icc (-Whitney.extremeIdx n) (Whitney.extremeIdx n)) := by
      rw [Fintype.mem_piFinset]
      intro i
      dsimp only [z]
      split_ifs <;> assumption
    rw [← descendant_indices l n] at hz
    obtain ⟨R, hR, he⟩ := Finset.mem_image.mp hz
    have he0 : R.index (pi 0) = p.1 := by rw [he]; simp [z]
    have he1 : R.index (pi 1) = p.2 := by rw [he]; simp [z]
    refine Finset.mem_image.mpr ⟨R, Finset.mem_filter.mpr ⟨hR, ?_⟩, ?_⟩
    · rwa [he0, he1]
    · exact Prod.ext he0 he1

/-- The precise contained-bin count is choose(3^n,2). No independent point
sampling or geometric probability is assumed in this count. -/
theorem triangle_contained_card (l : ℤ) (pi : Equiv.Perm (Fin 2)) (n : ℕ) :
    (triangleContainedCubes l pi n).card = (3 ^ n).choose 2 := by
  classical
  have hinj : Set.InjOn (fun R : TriadicCube 2 => (R.index (pi 0), R.index (pi 1)))
      (↑(triangleContainedCubes l pi n) : Set (TriadicCube 2)) := by
    intro Q hQ R hR he
    have hs := (scale_eq_sub_of_mem_descendantsAtDepth (Finset.mem_filter.mp hQ).1).trans
      (scale_eq_sub_of_mem_descendantsAtDepth (Finset.mem_filter.mp hR).1).symm
    have hi : Q.index = R.index := by
      funext i
      obtain ⟨j, rfl⟩ := pi.surjective i
      fin_cases j
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
    cases Q
    cases R
    cases hs
    cases hi
    rfl
  rw [← Finset.card_image_of_injOn hinj, triangle_contained_pairs, Finset.card_product_filter_lt]
  congr 1
  rw [Int.card_Icc]
  have he := Whitney.two_mul_extremeIdx_add_one n
  have hE := Whitney.extremeIdx_nonneg n
  have hp : (((3 : ℕ) ^ n : ℕ) : ℤ) = (3 : ℤ) ^ n := by push_cast; rfl
  omega

end ASDExplicitGamma.Inverse
