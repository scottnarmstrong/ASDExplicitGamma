module

public import ASDExplicitGamma.Inverse.StoppedPlanarGraph
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-! Genuine infinity-geodesics inside completely occupied aligned planar cubes. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open SimpleGraph

/-- An aligned discrete block cube contains exactly side consecutive indices
in each coordinate. -/
def blockCube (a : BlockSite) (side : ℕ) : Set BlockSite :=
  {x | ∀ d, a d ≤ x d ∧ x d < a d+(side:ℤ)}

/-- Move each coordinate one unit toward the target, simultaneously. -/
def blockStepToward (x y : BlockSite) : BlockSite := fun d =>
  if x d < y d then x d+1 else if y d < x d then x d-1 else x d

/-- A coordinate step stays between its two endpoint coordinates. -/
theorem block_step_between (x y : BlockSite) (d : Fin 2) :
    min (x d) (y d) ≤ blockStepToward x y d ∧
      blockStepToward x y d ≤ max (x d) (y d) := by
  unfold blockStepToward
  split_ifs <;> omega

/-- Simultaneous coordinate steps preserve the actual discrete cube. -/
theorem block_step_mem_cube (a : BlockSite) (side : ℕ) (x y : blockCube a side) :
    blockStepToward x.val y.val ∈ blockCube a side := by
  intro d
  have hx := x.property d
  have hy := y.property d
  have hh := block_step_between x.val y.val d
  omega

/-- Every coordinate distance drops by one unless it was already zero. -/
theorem block_step_distance (x y : BlockSite) (N : ℕ)
    (hN : ∀ d, |y d-x d| ≤ ((N+1:ℕ):ℤ)) :
    ∀ d, |y d-blockStepToward x y d| ≤ (N:ℤ) := by
  intro d
  have hh := abs_le.mp (hN d)
  unfold blockStepToward
  split_ifs <;> rw [abs_le] <;> constructor <;> omega

/-- A nontrivial simultaneous step is an actual edge of the planar graph. -/
theorem block_step_adj (x y : BlockSite) (hne : x ≠ y) :
    blockGraph.Adj x (blockStepToward x y) := by
  constructor
  · intro he
    apply hne
    funext d
    have hd := congrFun he d
    change x d = (if x d < y d then x d+1 else if y d < x d then x d-1 else x d) at hd
    split_ifs at hd <;> omega
  · intro d
    change |(if x d < y d then x d+1 else if y d < x d then x d-1 else x d)-x d| ≤ 1
    split_ifs <;> rw [abs_le] <;> constructor <;> omega

/-- The literal cube graph has a path no longer than the coordinate infinity
distance. Every vertex of the constructed path stays in the cube. -/
theorem cube_walk_length_le (a : BlockSite) (side N : ℕ)
    (x y : blockCube a side) (hN : ∀ d, |y.val d-x.val d| ≤ (N:ℤ)) :
    ∃ p : (blockGraph.induce (blockCube a side)).Walk x y, p.length ≤ N := by
  induction N generalizing x y with
  | zero =>
    have he : x = y := by
      apply Subtype.ext
      funext d
      have hh := abs_le.mp (hN d)
      omega
    subst y
    exact ⟨.nil,by simp⟩
  | succ N ih =>
    by_cases he : x = y
    · subst y
      exact ⟨.nil,by simp⟩
    let z : blockCube a side := ⟨blockStepToward x.val y.val,block_step_mem_cube a side x y⟩
    obtain ⟨p,hp⟩ := ih z y (block_step_distance x.val y.val N hN)
    have hadj : (blockGraph.induce (blockCube a side)).Adj x z :=
      block_step_adj x.val y.val (fun hh => he (Subtype.ext hh))
    exact ⟨p.cons hadj,by simpa only [Walk.length_cons] using Nat.add_le_add_right hp 1⟩

end ASDExplicitGamma.Inverse
