module

public import ASDExplicitGamma.Inverse.StoppedKuhnFinalMesh
public import ASDExplicitGamma.Inverse.ContainedTriangleRootResponse

/-! The literal hybrid dissection: untouched Whitney cubes and the actual
final Kuhn simplices of all active Whitney cubes. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Multiscale
noncomputable section

/-- Actual Whitney cells retaining their deterministic layer index. -/
def WhitneyIndexedCell (Q : TriadicCube 2) (H : ℕ) : Type :=
  Σ n : ℕ, ↥(whitneyRootLayer Q H n)

/-- Whole untouched cubes in the literal hybrid dissection. -/
def HybridIdentityCell (Q : TriadicCube 2) (H : ℕ) (S : Set (TriadicCube 2)) : Type :=
  {i : WhitneyIndexedCell Q H // ∀ V ∈ S, ¬ CubeTouch i.2.val V}

/-- Actual final simplices of active Whitney cubes. -/
def HybridActiveCell (Q : TriadicCube 2) (H : ℕ) (S : Set (TriadicCube 2)) : Type :=
  Σ i : {i : WhitneyIndexedCell Q H // ¬ (∀ V ∈ S, ¬ CubeTouch i.2.val V)},
    ↥(finalWhitneyKuhnCells Q H i.val.1 i.val.2.val)

/-- One countable hybrid family, chosen before every flux loading. -/
def HybridCell (Q : TriadicCube 2) (H : ℕ) (S : Set (TriadicCube 2)) : Type :=
  HybridIdentityCell Q H S ⊕ HybridActiveCell Q H S

instance whitneyIndexedCellCountable (Q : TriadicCube 2) (H : ℕ) : Countable (WhitneyIndexedCell Q H) :=
  inferInstanceAs (Countable (Σ n : ℕ, ↥(whitneyRootLayer Q H n)))

instance hybridIdentityCellCountable (Q : TriadicCube 2) (H : ℕ) (S : Set (TriadicCube 2)) :
    Countable (HybridIdentityCell Q H S) := inferInstanceAs (Countable {i : WhitneyIndexedCell Q H // ∀ V ∈ S, ¬ CubeTouch i.2.val V})

instance hybridActiveCellCountable (Q : TriadicCube 2) (H : ℕ) (S : Set (TriadicCube 2)) :
    Countable (HybridActiveCell Q H S) :=
  inferInstanceAs (Countable (Σ i : {i : WhitneyIndexedCell Q H // ¬ (∀ V ∈ S, ¬ CubeTouch i.2.val V)},
    ↥(finalWhitneyKuhnCells Q H i.val.1 i.val.2.val)))

instance hybridCellCountable (Q : TriadicCube 2) (H : ℕ) (S : Set (TriadicCube 2)) :
    Countable (HybridCell Q H S) :=
  inferInstanceAs (Countable (HybridIdentityCell Q H S ⊕ HybridActiveCell Q H S))

/-- The actual parent cube and its preserved layer index. -/
def hybridParent {Q : TriadicCube 2} {H : ℕ} {S : Set (TriadicCube 2)} :
    HybridCell Q H S → WhitneyIndexedCell Q H
  | .inl i => i.val
  | .inr i => i.1.val

/-- Physical observation domain of a hybrid cell. -/
def hybridDomain {Q : TriadicCube 2} {H : ℕ} {S : Set (TriadicCube 2)} :
    HybridCell Q H S → Book.Ch02.Domain 2
  | .inl i => Book.Ch02.cubeDomain i.val.2.val
  | .inr i => kuhnCellDomain i.2.val

/-- The actual Whitney parent cube uniquely determines its layer index. -/
theorem whitney_indexed_cube_injective (Q : TriadicCube 2) (H : ℕ) :
    Function.Injective (fun i : WhitneyIndexedCell Q H => i.2.val) := by
  intro ⟨n,P,hP⟩ ⟨m,R,hR⟩ he
  change P=R at he
  have hn := root_whitney_layer_scale Q H n hP
  have hm := root_whitney_layer_scale Q H m hR
  have hnm : n=m := by
    rw [he] at hn
    unfold whitneyProfile at hn hm
    omega
  subst m
  congr 1
  exact Subtype.ext he

/-- Each hybrid cell stays in its genuine Whitney parent interior. -/
theorem hybrid_domain_subset_parent {Q : TriadicCube 2} {H : ℕ} {S : Set (TriadicCube 2)}
    (i : HybridCell Q H S) :
    (hybridDomain i:Set (Vec 2)) ⊆ openCubeSet (hybridParent i).2.val := by
  cases i with
  | inl i => exact Set.Subset.rfl
  | inr i => exact final_kuhn_open_subset Q H i.1.val.1 i.1.val.2.property i.2.property

/-- Every hybrid observation domain lies inside the physical root. -/
theorem hybrid_domain_subset_root {Q : TriadicCube 2} {H : ℕ} {S : Set (TriadicCube 2)}
    (i : HybridCell Q H S) : (hybridDomain i:Set (Vec 2)) ⊆ openCubeSet Q :=
  (hybrid_domain_subset_parent i).trans
    (openCubeSet_subset_of_mem_descendantsAtDepth (root_whitney_layer_descendants Q H
      (hybridParent i).1 (hybridParent i).2.property))

end
end ASDExplicitGamma.Inverse
