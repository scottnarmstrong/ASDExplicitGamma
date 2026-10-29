module

public import ASDExplicitGamma.Inverse.StoppedCanonicalComponents
public import ASDExplicitGamma.Inverse.StoppedComponentMeshNodes

/-! Actual components are grouped by their canonical least neighborhood
layer. Every mesh group is finite because its nonempty node sets are disjoint. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- Distinct components are indexed by their actual cell sets, so choosing a
different root in the same component introduces no duplicate. -/
def componentFamily (S : Set (TriadicCube 2)) : Set (Set (TriadicCube 2)) :=
  {C | ∃ R ∈ S, C = badComponent S R}

/-- The source common-mesh group with least neighborhood layer a. -/
def rootComponentGroup (Q : TriadicCube 2) (H : ℕ) (S : Set (TriadicCube 2)) (a : ℕ) :
    Set (Set (TriadicCube 2)) :=
  {C | C ∈ componentFamily S ∧ rootComponentLeastLayer Q H C = a}

theorem component_family_nodes_disjoint (Q : TriadicCube 2) (J : ℕ)
    (S : Set (TriadicCube 2)) (C D : Set (TriadicCube 2))
    (hC : C ∈ componentFamily S) (hD : D ∈ componentFamily S) (hne : C ≠ D) :
    Disjoint (componentMeshNodes Q J C) (componentMeshNodes Q J D) := by
  obtain ⟨R,hR,rfl⟩ := hC
  obtain ⟨T,hT,rfl⟩ := hD
  exact distinct_component_mesh_nodes_disjoint Q J S R T hne

/-- Every component in a source mesh group has a nonempty actual common-mesh
node set. The geometric conditions come from the stopped-chain theorem. -/
theorem stopped_component_group_nodes_nonempty (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (a : ℕ) {C : Set (TriadicCube 2)} (hC : C ∈ rootComponentGroup Q H S a) :
    (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C).Nonempty := by
  obtain ⟨R,hR,he⟩ := hC.1
  have hleast := hC.2
  subst C
  have ht := (stopped_component_lifted_paths M Q H hH τ η ω hgood S hS hbad R hR).2
  change ∀ D ∈ rootWhitneyNeighborhood Q H (badComponent S R),
    D ∈ whitneyRootLayer Q H (rootComponentLeastLayer Q H (badComponent S R)) ∨
    D ∈ whitneyRootLayer Q H (rootComponentLeastLayer Q H (badComponent S R)+1) at ht
  rw [hleast] at ht
  apply component_mesh_nodes_nonempty Q H a (badComponent S R) ⟨R,self_mem_badComponent hR⟩
  intro V hV
  exact ht V ⟨hS hV.1,V,hV,cubeTouch_refl V⟩

/-- Finiteness of a common-mesh component group is a consequence of actual
node nonemptiness and component disjointness, with no finite-cluster or
finite-group premise. -/
theorem stopped_component_group_finite (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V) (a : ℕ) :
    (rootComponentGroup Q H S a).Finite := by
  classical
  let J := compatibleWhitneyMeshDepth H (a+1)
  have hne (C : rootComponentGroup Q H S a) : (componentMeshNodes Q J C.val).Nonempty :=
    stopped_component_group_nodes_nonempty M Q H hH τ η ω hgood S hS hbad a C.property
  let f : rootComponentGroup Q H S a → InteriorNode J := fun C => Classical.choose (hne C)
  have hf (C : rootComponentGroup Q H S a) : f C ∈ componentMeshNodes Q J C.val := Classical.choose_spec (hne C)
  have hi : Function.Injective f := by
    intro C D he
    apply Subtype.ext
    by_contra hCD
    have hd := component_family_nodes_disjoint Q J S C.val D.val C.property.1 D.property.1 hCD
    exact Finset.disjoint_left.mp hd (hf C) (by rw [he]; exact hf D)
  let stoppedComponentGroupFinite : Finite (rootComponentGroup Q H S a) := Finite.of_injective f hi
  exact Set.toFinite _

end
end ASDExplicitGamma.Inverse
