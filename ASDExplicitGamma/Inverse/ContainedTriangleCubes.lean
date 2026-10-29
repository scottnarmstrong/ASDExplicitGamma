module

public import ASDExplicitGamma.Inverse.WhitneyInteriorCount
public import Algsuperdiff.Section3.Provider.Whitney.KuhnCells

/-! Actual contained triadic cubes in planar ordered-coordinate Kuhn triangles. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
open Algsuperdiff.Section3.Provider

/-- The depth-n cubes whose two coordinate bins are strictly ordered.
These are the literal contained cubes of the source's planar Kuhn triangle. -/
noncomputable def triangleContainedCubes (l : ℤ) (pi : Equiv.Perm (Fin 2)) (n : ℕ) :
    Finset (TriadicCube 2) :=
  (descendantsAtDepth (originCube 2 l) n).filter (fun R => R.index (pi 0) < R.index (pi 1))

/-- Every selected contained cube lies in the canonical half-open triangle;
the proof retains the actual parent and its coordinate ordering. -/
theorem triangle_contained_cube (l : ℤ) (pi : Equiv.Perm (Fin 2)) (n : ℕ)
    {R : TriadicCube 2} (hR : R ∈ triangleContainedCubes l pi n) :
    cubeSet R ⊆ ({supportCube := originCube 2 l, order := pi} : Whitney.KuhnCell 2).carrier := by
  obtain ⟨hRd, hRo⟩ := Finset.mem_filter.mp hR
  intro x hx
  have hscale : 0 < cubeScaleFactor R := zpow_pos (by norm_num) _
  have hp := hx (pi 0)
  have hq := hx (pi 1)
  have hidx : (R.index (pi 0) : ℝ) + 1 ≤ (R.index (pi 1) : ℝ) := by
    exact_mod_cast (show R.index (pi 0) + 1 ≤ R.index (pi 1) by omega)
  have hm := mul_le_mul_of_nonneg_right hidx hscale.le
  have hxy : x (pi 0) < x (pi 1) := by
    change ((R.index (pi 0) : ℝ) - 1 / 2) * cubeScaleFactor R ≤ x (pi 0) ∧
      x (pi 0) < ((R.index (pi 0) : ℝ) + 1 / 2) * cubeScaleFactor R at hp
    change ((R.index (pi 1) : ℝ) - 1 / 2) * cubeScaleFactor R ≤ x (pi 1) ∧
      x (pi 1) < ((R.index (pi 1) : ℝ) + 1 / 2) * cubeScaleFactor R at hq
    linarith only [hp.2, hq.1, hm]
  have hord : Whitney.triadicLocalCoordinate (originCube 2 l) x (pi 0) <
      Whitney.triadicLocalCoordinate (originCube 2 l) x (pi 1) := by
    simpa only [Whitney.triadicLocalCoordinate, originCube, Pi.zero_apply, Int.cast_zero, zero_mul, sub_zero] using hxy
  refine ⟨cubeSet_subset_of_mem_descendantsAtDepth hRd hx, ?_⟩
  apply (Tuple.eq_sort_iff (f := Whitney.triadicLocalCoordinate (originCube 2 l) x)
    (σ := pi)).mpr
  constructor
  · intro i j hij
    change Whitney.triadicLocalCoordinate (originCube 2 l) x (pi i) ≤
      Whitney.triadicLocalCoordinate (originCube 2 l) x (pi j)
    by_cases he : i = j
    · subst j; exact le_rfl
    · have hi : i = 0 := Fin.ext (by omega)
      have hj : j = 1 := Fin.ext (by omega)
      simpa only [hi, hj] using hord.le
  · intro i j hij he
    change Whitney.triadicLocalCoordinate (originCube 2 l) x (pi i) =
      Whitney.triadicLocalCoordinate (originCube 2 l) x (pi j) at he
    have hi : i = 0 := Fin.ext (by omega)
    have hj : j = 1 := Fin.ext (by omega)
    rw [hi, hj] at he
    exact False.elim (hord.ne he)

end ASDExplicitGamma.Inverse
