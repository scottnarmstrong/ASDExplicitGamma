module

public import ASDExplicitGamma.Inverse.StoppedFineBlockMap
public import ASDExplicitGamma.Inverse.StoppedClusterReach

/-! The fine two-neighbor paths map to actual occupied block components. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open SimpleGraph

/-- The source fine-grid graph allows coordinate steps up to two. -/
def fineGraph : SimpleGraph BlockSite where
  Adj x y := x ≠ y ∧ ∀ d, |y d-x d| ≤ 2
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm,fun d => ?_⟩
    simpa only [abs_sub_comm] using h.2 d⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

/-- Taking blocks may collapse an edge, but it preserves connectivity within
the actual occupied induced graph. -/
theorem fine_reachable_blocks {F O : Set BlockSite}
    (hFO : ∀ x ∈ F, fineBlockIndex x ∈ O) {x y : F}
    (hxy : (fineGraph.induce F).Reachable x y) :
    (blockGraph.induce O).Reachable ⟨fineBlockIndex x.val,hFO x.val x.property⟩
      ⟨fineBlockIndex y.val,hFO y.val y.property⟩ := by
  let f : F → O := fun z => ⟨fineBlockIndex z.val,hFO z.val z.property⟩
  obtain ⟨p⟩ := hxy
  change (blockGraph.induce O).Reachable (f x) (f y)
  induction p with
  | nil => exact Reachable.rfl
  | @cons x y z h p ih =>
    have hstep : (blockGraph.induce O).Reachable (f x) (f y) := by
      by_cases he : fineBlockIndex x.val = fineBlockIndex y.val
      · have hf : f x = f y := Subtype.ext he
        rw [hf]
      · apply Adj.reachable
        exact ⟨he,fine_block_index_neighbor x.val y.val h.2⟩
    exact hstep.trans ih

/-- The complete preimage of the occupied block field, a deterministic
majorant for all its extended bad fine cells. -/
def fineOccupied {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω) : Set BlockSite :=
  fineBlockIndex ⁻¹' markedOccupied B ω

/-- An occupied fine path with a distant block endpoint is included in the
literal block-cluster radius event, including collapsed repeated block sites. -/
theorem fine_reachable_reaches {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω)
    {x y : fineOccupied B ω}
    (hxy : (fineGraph.induce (fineOccupied B ω)).Reachable x y)
    (R : ℕ) (hR : ∃ d, (R:ℤ) ≤ |fineBlockIndex y.val d-fineBlockIndex x.val d|) :
    ω ∈ clusterReaches B (fineBlockIndex x.val) R := by
  exact ⟨x.property,⟨fineBlockIndex y.val,y.property⟩,
    fine_reachable_blocks (fun _ hx => hx) hxy,hR⟩

end ASDExplicitGamma.Inverse
