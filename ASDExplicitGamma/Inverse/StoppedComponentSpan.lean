module

public import ASDExplicitGamma.Inverse.StoppedClusterSpan
public import ASDExplicitGamma.Inverse.StoppedComponentMeshNodes
public import ASDExplicitGamma.Inverse.StoppedWhitneyLift

/-! Component midpoint coordinate spans consume the actual physical cluster
diameter, keeping the factor 2*3^40 and all closed-cell endpoints exactly. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3.Provider
open ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- Actual physical block observations bound the exact midpoint coordinate
range of a finite nonempty node set. -/
theorem component_coordinate_span_of_block_observations {Ω : Type*}
    (B : PlanarMarks Ω) (ω : Ω) (j : ℤ) (x r : BlockSite)
    (hr : ∀ d, |r d-x d| ≤ 2) (hfinite : diameterField B ω x ≠ ∞)
    (Q : TriadicCube 2) (J : ℕ) (C : Finset (InteriorNode J)) (hne : C.Nonempty)
    (hobs : ∀ z ∈ C, ∃ u ∈ clusterSites B ω r,
      diagInteriorVertex Q J z ∈ physicalBlockRegion j u 1) (i : Fin 2) :
    componentCoordinateMax Q J C hne i-componentCoordinateMin Q J C hne i ≤
      2*(3:ℝ)^40*realDiameterField B x ω*(3:ℝ)^j := by
  have hlow : componentCoordinateMin Q J C hne i ∈ componentCoordinateSet Q J C i :=
    Finset.min'_mem _ _
  have hhigh : componentCoordinateMax Q J C hne i ∈ componentCoordinateSet Q J C i :=
    Finset.max'_mem _ _
  obtain ⟨zl,hzl,hel⟩ := Finset.mem_image.mp hlow
  obtain ⟨zh,hzh,heh⟩ := Finset.mem_image.mp hhigh
  obtain ⟨u,hu,hpu⟩ := hobs zh hzh
  obtain ⟨v,hv,hpv⟩ := hobs zl hzl
  have hh := physical_cluster_point_span B ω j x r u v hr hfinite hu hv hpu hpv i
  rw [hel,heh] at hh
  exact (le_abs_self _).trans hh

/-- Every common-mesh component node observes the same actual physical
cluster as its lifted parent, including boundary nodes of smaller cells. -/
theorem component_mesh_nodes_in_parent_blocks {Ω : Type*}
    (B : PlanarMarks Ω) (ω : Ω) (j : ℤ) (r : BlockSite)
    (Q : TriadicCube 2) (J : ℕ) (C : Set (TriadicCube 2))
    (hlift : ∀ V ∈ C, ∃ A : TriadicCube 2, ∃ n : ℕ,
      V ∈ descendantsAtDepth A n ∧ A.scale=j ∧ fineBlockIndex A.index ∈ clusterSites B ω r)
    {z : InteriorNode J} (hz : z ∈ componentMeshNodes Q J C) :
    ∃ u ∈ clusterSites B ω r, diagInteriorVertex Q J z ∈ physicalBlockRegion j u 1 := by
  obtain ⟨V,hV,hzV⟩ := (component_mesh_nodes_mem _ _ _ _).mp hz
  obtain ⟨A,n,hVA,hAj,hA⟩ := hlift V hV
  refine ⟨fineBlockIndex A.index,hA,?_⟩
  have hparent := descendant_closed_cube_subset hVA hzV
  have he : (⟨j,A.index⟩ : TriadicCube 2) = A := by
    cases A with
    | mk scale index =>
      change scale=j at hAj
      subst scale
      rfl
  exact fine_parent_closed_in_block j A.index (by simpa only [he] using hparent)

/-- Exact source physical span of the actual component node set, derived
from lifted occupied component membership rather than assumed as a wave or
density bound. -/
theorem component_mesh_coordinate_span {Ω : Type*}
    (B : PlanarMarks Ω) (ω : Ω) (j : ℤ) (x r : BlockSite)
    (hr : ∀ d, |r d-x d| ≤ 2) (hfinite : diameterField B ω x ≠ ∞)
    (Q : TriadicCube 2) (J : ℕ) (C : Set (TriadicCube 2))
    (hne : (componentMeshNodes Q J C).Nonempty)
    (hlift : ∀ V ∈ C, ∃ A : TriadicCube 2, ∃ n : ℕ,
      V ∈ descendantsAtDepth A n ∧ A.scale=j ∧ fineBlockIndex A.index ∈ clusterSites B ω r)
    (i : Fin 2) :
    componentCoordinateMax Q J (componentMeshNodes Q J C) hne i-
      componentCoordinateMin Q J (componentMeshNodes Q J C) hne i ≤
      2*(3:ℝ)^40*realDiameterField B x ω*(3:ℝ)^j :=
  component_coordinate_span_of_block_observations B ω j x r hr hfinite Q J _ hne
    (fun _ hz => component_mesh_nodes_in_parent_blocks B ω j r Q J C hlift hz) i

end
end ASDExplicitGamma.Inverse
