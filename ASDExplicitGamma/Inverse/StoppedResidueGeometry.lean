module

public import ASDExplicitGamma.Inverse.StoppedAlignedCubes
public import Mathlib.Tactic.Linarith

/-! The literal nine residue classes separate complete positive-activation observation cubes. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- The actual two-coordinate residue class modulo three. -/
def blockResidue (i : BlockSite) : Fin 2 → Fin 3 := fun d =>
  ⟨(i d%3).toNat,by
    have h0 := Int.emod_nonneg (i d) (by norm_num : (3:ℤ) ≠ 0)
    have h1 := Int.emod_lt_of_pos (i d) (by norm_num : (0:ℤ) < 3)
    omega⟩

/-- Distinct indices of one residue class differ by at least three in a coordinate. -/
theorem block_residue_separation (i j : BlockSite) (hne : i ≠ j)
    (hcolor : blockResidue i = blockResidue j) :
    ∃ d, (3:ℤ) ≤ |j d-i d| := by
  by_contra! hclose
  apply hne
  funext d
  have hc := congrArg Fin.val (congrFun hcolor d)
  change (i d%3).toNat = (j d%3).toNat at hc
  have h0 := Int.emod_nonneg (i d) (by norm_num : (3:ℤ) ≠ 0)
  have h1 := Int.emod_nonneg (j d) (by norm_num : (3:ℤ) ≠ 0)
  have hd := abs_lt.mp (hclose d)
  omega

/-- A coordinate gap of three aligned indices gives a strictly larger than
two-side gap between every pair of actual sites in the two observation cubes. -/
theorem aligned_cube_coordinate_gap (side : ℕ) (hs : 0 < side)
    (i j x y : BlockSite) (d : Fin 2) (hij : 3 ≤ j d-i d)
    (hx : x ∈ blockCube (alignedCubeBase side i) side)
    (hy : y ∈ blockCube (alignedCubeBase side j) side) :
    2*(side:ℤ) < y d-x d := by
  have hx' : x d < (side:ℤ)*i d+(side:ℤ) := (hx d).2
  have hy' : (side:ℤ)*j d ≤ y d := (hy d).1
  have hsZ : (0:ℤ) < side := by exact_mod_cast hs
  have hm := mul_le_mul_of_nonneg_left hij hsZ.le
  nlinarith only [hx',hy',hm]

/-- Complete same-color cube populations are separated, rather than only
the selected raw-mark locations. This is the restriction-independence input. -/
theorem same_color_cube_sites_separated (side : ℕ) (hs : 0 < side)
    (i j : BlockSite) (hne : i ≠ j) (hc : blockResidue i = blockResidue j)
    (x y : BlockSite)
    (hx : x ∈ blockCube (alignedCubeBase side i) side)
    (hy : y ∈ blockCube (alignedCubeBase side j) side) :
    ∃ d, 2*(side:ℤ) < |y d-x d| := by
  obtain ⟨d,hd⟩ := block_residue_separation i j hne hc
  refine ⟨d,?_⟩
  by_cases hij : i d ≤ j d
  · rw [abs_of_nonneg (sub_nonneg.mpr hij)] at hd
    exact (aligned_cube_coordinate_gap side hs i j x y d hd hx hy).trans_le (le_abs_self _)
  · have hji : j d ≤ i d := le_of_lt (lt_of_not_ge hij)
    rw [abs_of_nonpos (sub_nonpos.mpr hji),neg_sub] at hd
    have hh := aligned_cube_coordinate_gap side hs j i y x d hd hy hx
    exact hh.trans_le (by simpa only [abs_sub_comm] using le_abs_self (x d-y d))

end ASDExplicitGamma.Inverse
