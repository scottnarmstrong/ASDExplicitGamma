module

public import ASDExplicitGamma.Inverse.StoppedCellMeshVertices

/-! Actual component node sets on their source common meshes, including
every cell corner and the physical disjointness needed by midpoint maps. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney ASDExplicitGamma.Triadic
noncomputable section

/-- All common-mesh nodes on the actual closed component cells. -/
def componentMeshNodes (Q : TriadicCube 2) (J : ℕ) (C : Set (TriadicCube 2)) :
    Finset (InteriorNode J) := by
  classical
  exact Finset.univ.filter (fun z => ∃ V ∈ C,
    diagInteriorVertex Q J z ∈ Metric.closedBall (cubeCenter V) (cubeRadius V))

theorem component_mesh_nodes_mem (Q : TriadicCube 2) (J : ℕ) (C : Set (TriadicCube 2))
    (z : InteriorNode J) : z ∈ componentMeshNodes Q J C ↔
      ∃ V ∈ C, diagInteriorVertex Q J z ∈ Metric.closedBall (cubeCenter V) (cubeRadius V) := by
  classical
  simp only [componentMeshNodes,Finset.mem_filter,Finset.mem_univ,true_and]

/-- Every actual corner of every cell in the confined component occurs on
the finer of its two source meshes. -/
theorem component_mesh_contains_cell_corners (Q : TriadicCube 2) (H a : ℕ)
    (C : Set (TriadicCube 2))
    (hC : ∀ V ∈ C, V ∈ whitneyRootLayer Q H a ∨ V ∈ whitneyRootLayer Q H (a+1))
    {V : TriadicCube 2} (hV : V ∈ C) (ε : Fin 2 → Fin 2) :
    ∃ z ∈ componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C,
      diagInteriorVertex Q (compatibleWhitneyMeshDepth H (a+1)) z = cellCornerVertex V ε := by
  obtain ⟨n,hn,hnV⟩ : ∃ n, (n=a ∨ n=a+1) ∧ V ∈ whitneyRootLayer Q H n := by
    rcases hC V hV with h | h
    · exact ⟨a,Or.inl rfl,h⟩
    · exact ⟨a+1,Or.inr rfl,h⟩
  have hdepth : compatibleWhitneyMeshDepth H n ≤ compatibleWhitneyMeshDepth H (a+1) := by
    rcases hn with rfl | rfl
    · unfold compatibleWhitneyMeshDepth whitneyProfile
      omega
    · exact le_rfl
  have hdesc : V ∈ descendantsAtDepth Q (compatibleWhitneyMeshDepth H n) :=
    root_whitney_layer_descendants Q H n hnV
  obtain ⟨z,hz⟩ := cell_corner_interior_node Q hdesc (root_whitney_closed_cell_interior Q H n hnV) ε
  refine ⟨refineInteriorNode hdepth z,?_,?_⟩
  · rw [component_mesh_nodes_mem]
    refine ⟨V,hV,?_⟩
    rw [refine_interior_vertex,hz]
    exact cell_corner_vertex_closed V ε
  · rw [refine_interior_vertex,hz]

/-- Nonempty actual confined components give nonempty midpoint node sets. -/
theorem component_mesh_nodes_nonempty (Q : TriadicCube 2) (H a : ℕ)
    (C : Set (TriadicCube 2)) (hne : C.Nonempty)
    (hC : ∀ V ∈ C, V ∈ whitneyRootLayer Q H a ∨ V ∈ whitneyRootLayer Q H (a+1)) :
    (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C).Nonempty := by
  obtain ⟨V,hV⟩ := hne
  obtain ⟨z,hz,he⟩ := component_mesh_contains_cell_corners Q H a C hC hV (fun _ => 0)
  exact ⟨z,hz⟩

/-- Touching cells in two components force equality of those components. -/
theorem bad_components_eq_of_touch (S : Set (TriadicCube 2)) (R T : TriadicCube 2)
    {V W : TriadicCube 2} (hV : V ∈ badComponent S R) (hW : W ∈ badComponent S T)
    (ht : CubeTouch V W) : badComponent S R = badComponent S T := by
  have hRT : BadChain S R T := hV.2.trans
    ((Relation.ReflTransGen.single ⟨hV.1,hW.1,ht⟩).trans (badChain_symm hW.2))
  ext X
  constructor
  · intro hX
    exact ⟨hX.1,(badChain_symm hRT).trans hX.2⟩
  · intro hX
    exact ⟨hX.1,hRT.trans hX.2⟩

/-- Distinct actual components have disjoint node sets on every common
mesh; boundary vertices are included in this assertion. -/
theorem distinct_component_mesh_nodes_disjoint (Q : TriadicCube 2) (J : ℕ)
    (S : Set (TriadicCube 2)) (R T : TriadicCube 2)
    (hne : badComponent S R ≠ badComponent S T) :
    Disjoint (componentMeshNodes Q J (badComponent S R)) (componentMeshNodes Q J (badComponent S T)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro z hzR hzT
  obtain ⟨V,hV,hzV⟩ := (component_mesh_nodes_mem _ _ _ _).mp hzR
  obtain ⟨W,hW,hzW⟩ := (component_mesh_nodes_mem _ _ _ _).mp hzT
  exact hne (bad_components_eq_of_touch S R T hV hW ⟨_,hzV,hzW⟩)

end
end ASDExplicitGamma.Inverse
