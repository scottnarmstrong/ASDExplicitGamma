module

public import ASDExplicitGamma.Inverse.ContainedTriangleFirst
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Coverage by the full first-contained triadic cube family. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Filter
open scoped Topology

/-- Every strictly ordered point eventually has a contained coordinate-bin cube. -/
theorem triangle_eventually_contained (l : ℤ) (pi : Equiv.Perm (Fin 2))
    (x : Vec 2) (hx : x ∈ cubeSet (originCube 2 l)) (hxy : x (pi 0) < x (pi 1)) :
    ∃ n : ℕ, ∃ R ∈ triangleContainedCubes l pi n, x ∈ cubeSet R := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1)).const_mul ((3 : ℝ) ^ l)
  have he : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ^ l * (1 / 3 : ℝ) ^ n < x (pi 1) - x (pi 0) := by
    apply (tendsto_order.mp (by simpa only [mul_zero] using ht)).2
    exact sub_pos.mpr hxy
  obtain ⟨n, hn⟩ := he.exists
  obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet n hx
  refine ⟨n, R, Finset.mem_filter.mpr ⟨hR, ?_⟩, hxR⟩
  by_contra ho
  have hi : (R.index (pi 1) : ℝ) ≤ (R.index (pi 0) : ℝ) := by
    exact_mod_cast (le_of_not_gt ho)
  have hs : 0 < cubeScaleFactor R := zpow_pos (by norm_num) _
  have hm := mul_le_mul_of_nonneg_right hi hs.le
  have hp := (hxR (pi 0)).1
  have hq := (hxR (pi 1)).2
  have hside : cubeScaleFactor R = (3 : ℝ) ^ l * (1 / 3 : ℝ) ^ n := by
    have hscale : R.scale = l - (n : ℤ) := scale_eq_sub_of_mem_descendantsAtDepth hR
    rw [cubeScaleFactor, hscale, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    simp only [div_eq_mul_inv, one_mul, inv_pow]
  change ((R.index (pi 0) : ℝ) - 1 / 2) * cubeScaleFactor R ≤ x (pi 0) at hp
  change x (pi 1) < ((R.index (pi 1) : ℝ) + 1 / 2) * cubeScaleFactor R at hq
  rw [← hside] at hn
  linarith only [hm, hp, hq, hn]

/-- First containment is genuinely achieved at a positive finite depth. -/
theorem triangle_first_cover (l : ℤ) (pi : Equiv.Perm (Fin 2))
    (x : Vec 2) (hx : x ∈ cubeSet (originCube 2 l)) (hxy : x (pi 0) < x (pi 1)) :
    ∃ n : ℕ, ∃ R ∈ triangleFirstCubes l pi n, x ∈ cubeSet R := by
  classical
  have hp := triangle_eventually_contained l pi x hx hxy
  let N := Nat.find hp
  obtain ⟨R, hR, hxR⟩ := Nat.find_spec hp
  have hNpos : 0 < N := by
    by_contra hh
    have hN : Nat.find hp = 0 := by change N = 0; omega
    rw [hN] at hR
    have he : R = originCube 2 l := by
      simpa only [descendantsAtDepth_zero, Finset.mem_singleton] using
        (Finset.mem_filter.mp hR).1
    have ho := (Finset.mem_filter.mp hR).2
    subst R
    simp only [originCube, Pi.zero_apply, lt_self_iff_false] at ho
  have hNs : N - 1 + 1 = N := by omega
  have hR' : R ∈ triangleContainedCubes l pi (N - 1 + 1) := by
    rw [hNs]
    exact hR
  refine ⟨N - 1, R, Finset.mem_filter.mpr ⟨hR', ?_⟩, hxR⟩
  intro hparent
  obtain ⟨A, _, hRA⟩ := mem_descendantsAtDepth_succ_iff.mp (Finset.mem_filter.mp hR').1
  have hpar : parentCube R = A := by
    obtain ⟨digits, rfl⟩ := mem_childCubes_iff.mp hRA
    exact childCube_parent A digits
  have hxA := cubeSet_subset_of_mem_childCubes hRA hxR
  have hxP : x ∈ cubeSet (parentCube R) := by rwa [hpar]
  exact Nat.find_min hp (by change N - 1 < N; omega) ⟨parentCube R, hparent, hxP⟩

/-- Every descendant of a contained cube remains contained in the triangle. -/
theorem triangle_descendant_contained (l : ℤ) (pi : Equiv.Perm (Fin 2)) (n d : ℕ)
    {A R : TriadicCube 2} (hA : A ∈ triangleContainedCubes l pi n)
    (hR : R ∈ descendantsAtDepth A d) : R ∈ triangleContainedCubes l pi (n + d) := by
  induction d generalizing R with
  | zero =>
    have he : R = A := by
      simpa only [descendantsAtDepth_zero, Finset.mem_singleton] using hR
    simpa only [Nat.add_zero, he] using hA
  | succ d ih =>
    obtain ⟨B, hB, hRB⟩ := mem_descendantsAtDepth_succ_iff.mp hR
    simpa only [Nat.add_assoc] using triangle_child_contained l pi (n + d) (ih hB) hRB

/-- All first-contained cubes, over all depths. -/
def triangleCubePartition (l : ℤ) (pi : Equiv.Perm (Fin 2)) : Set (TriadicCube 2) :=
  {R | ∃ n : ℕ, R ∈ triangleFirstCubes l pi n}

end ASDExplicitGamma.Inverse
