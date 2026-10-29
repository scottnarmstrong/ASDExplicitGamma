module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

/-! The actual planar infinity-neighbor block lattice used by stopped clusters. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- Physical block indices, before multiplying by the source block side. -/
abbrev BlockSite := Fin 2 → ℤ

/-- The literal 3-by-3 closed block neighborhood. -/
def blockBox (x : BlockSite) : Finset BlockSite :=
  Finset.univ.image (fun a : Fin 2 → Fin 3 => fun d => x d+(a d).val-1)

/-- Two distinct blocks touch precisely when each coordinate differs by at most one. -/
def blockGraph : SimpleGraph BlockSite where
  Adj x y := x ≠ y ∧ ∀ d, |y d-x d| ≤ 1
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm, fun d => ?_⟩
    simpa only [abs_sub_comm] using h.2 d⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

/-- Membership is the exact coordinate infinity-distance condition. -/
theorem mem_block_box (x y : BlockSite) :
    y ∈ blockBox x ↔ ∀ d, |y d-x d| ≤ 1 := by
  constructor
  · intro hy
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hy
    intro d
    have hh := (a d).isLt
    change |(x d+(a d).val-1)-x d| ≤ 1
    rw [abs_le]
    constructor <;> omega
  · intro hy
    let a : Fin 2 → Fin 3 := fun d => ⟨(y d-x d+1).toNat, by
      have hh := abs_le.mp (hy d)
      omega⟩
    apply Finset.mem_image.mpr
    refine ⟨a,Finset.mem_univ _,?_⟩
    funext d
    have hh := abs_le.mp (hy d)
    have hn : 0 ≤ y d-x d+1 := by omega
    have he := Int.toNat_of_nonneg hn
    change x d+((y d-x d+1).toNat:ℤ)-1 = y d
    omega

/-- Every block has exactly nine sites in its closed unit neighborhood. -/
theorem block_box_card (x : BlockSite) : (blockBox x).card = 9 := by
  have hi : Function.Injective (fun a : Fin 2 → Fin 3 => fun d => x d+(a d).val-1) := by
    intro a b hab
    funext d
    apply Fin.ext
    have hh : x d+(a d).val-1 = x d+(b d).val-1 := congrFun hab d
    omega
  rw [blockBox, Finset.card_image_of_injective _ hi]
  norm_num

/-- The center is present; deleting it gives the exact eight neighbors. -/
theorem center_mem_block_box (x : BlockSite) : x ∈ blockBox x := by
  rw [mem_block_box]
  simp

/-- The finite neighbor enumeration contains exactly the genuine graph neighbors. -/
theorem block_neighbor_iff (x y : BlockSite) :
    y ∈ (blockBox x).erase x ↔ blockGraph.Adj x y := by
  change y ∈ (blockBox x).erase x ↔ x ≠ y ∧ ∀ d, |y d-x d| ≤ 1
  rw [Finset.mem_erase, mem_block_box]
  exact and_congr ne_comm Iff.rfl

/-- The planar infinity-neighbor graph has degree eight, without extra inflation. -/
theorem block_neighbor_card (x : BlockSite) : ((blockBox x).erase x).card = 8 := by
  rw [Finset.card_erase_of_mem (center_mem_block_box x),block_box_card]

/-- The genuine graph neighbor set is finite, through the exact eight-site enumeration. -/
instance blockGraphLocallyFinite : blockGraph.LocallyFinite := fun x =>
  Fintype.ofFinset ((blockBox x).erase x) (fun y => block_neighbor_iff x y)

/-- The graph degree itself equals eight. -/
theorem block_graph_degree (x : BlockSite) : blockGraph.degree x = 8 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_ofFinset ((blockBox x).erase x) (fun y => block_neighbor_iff x y)).trans
    (block_neighbor_card x)

end ASDExplicitGamma.Inverse
