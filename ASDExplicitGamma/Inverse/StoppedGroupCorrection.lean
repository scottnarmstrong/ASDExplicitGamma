module

public import ASDExplicitGamma.Inverse.StoppedComponentGroups

/-! Geometry-only nodal corrections for each actual finite common-mesh
component group. Distinct components receive one unambiguous midpoint. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization ASDExplicitGamma.Triadic
noncomputable section

/-- The actual common-mesh group's nodal midpoint displacement. -/
def rootGroupNodalCorrection (Q : TriadicCube 2) (H : ℕ) (S : Set (TriadicCube 2)) (a : ℕ)
    (hfin : (rootComponentGroup Q H S a).Finite)
    (hne : ∀ C : rootComponentGroup Q H S a,
      (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val).Nonempty)
    (i : Fin 2) : InteriorNode (compatibleWhitneyMeshDepth H (a+1)) → ℝ := by
  classical
  letI stoppedGroupNodalFintype := hfin.fintype
  exact midpointNodalCorrection (ι := rootComponentGroup Q H S a) Q
    (compatibleWhitneyMeshDepth H (a+1))
    (fun C : rootComponentGroup Q H S a =>
      componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val) hne i

/-- The actual finite source group's zero-trace coordinate correction. -/
def rootGroupCorrection (Q : TriadicCube 2) (H : ℕ) (S : Set (TriadicCube 2)) (a : ℕ)
    (hfin : (rootComponentGroup Q H S a).Finite)
    (hne : ∀ C : rootComponentGroup Q H S a,
      (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val).Nonempty)
    (i : Fin 2) : H1Function (openCubeSet Q) :=
  diagSynthesisH1Linear Q (compatibleWhitneyMeshDepth H (a+1)) (rootGroupNodalCorrection Q H S a hfin hne i)

theorem root_group_nodal_on_component (Q : TriadicCube 2) (H : ℕ) (S : Set (TriadicCube 2)) (a : ℕ)
    (hfin : (rootComponentGroup Q H S a).Finite)
    (hne : ∀ C : rootComponentGroup Q H S a,
      (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val).Nonempty)
    (C : rootComponentGroup Q H S a)
    {z : InteriorNode (compatibleWhitneyMeshDepth H (a+1))}
    (hz : z ∈ componentMeshNodes Q _ C.val) (i : Fin 2) :
    rootGroupNodalCorrection Q H S a hfin hne i z =
      componentMidpoint Q _ (componentMeshNodes Q _ C.val) (hne C) i-
        diagInteriorVertex Q (compatibleWhitneyMeshDepth H (a+1)) z i := by
  classical
  let stoppedGroupNodalFintype := hfin.fintype
  have hdisj (C D : rootComponentGroup Q H S a) (hCD : C ≠ D) :
      Disjoint (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val)
        (componentMeshNodes Q _ D.val) :=
    component_family_nodes_disjoint Q _ S C.val D.val C.property.1 D.property.1
      (fun he => hCD (Subtype.ext he))
  exact midpoint_nodal_correction_on_component Q (compatibleWhitneyMeshDepth H (a+1))
    (fun D : rootComponentGroup Q H S a =>
      componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) D.val) hne hdisj C hz i

theorem root_group_nodal_off_components (Q : TriadicCube 2) (H : ℕ) (S : Set (TriadicCube 2)) (a : ℕ)
    (hfin : (rootComponentGroup Q H S a).Finite)
    (hne : ∀ C : rootComponentGroup Q H S a,
      (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val).Nonempty)
    (i : Fin 2) {z : InteriorNode (compatibleWhitneyMeshDepth H (a+1))}
    (hz : ∀ C : rootComponentGroup Q H S a, z ∉ componentMeshNodes Q _ C.val) :
    rootGroupNodalCorrection Q H S a hfin hne i z = 0 := by
  classical
  let stoppedGroupNodalFintype := hfin.fintype
  exact midpoint_nodal_correction_off_components Q (compatibleWhitneyMeshDepth H (a+1))
    (fun D : rootComponentGroup Q H S a =>
      componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) D.val) hne i hz

theorem root_group_nodal_nonzero_component (Q : TriadicCube 2) (H : ℕ) (S : Set (TriadicCube 2)) (a : ℕ)
    (hfin : (rootComponentGroup Q H S a).Finite)
    (hne : ∀ C : rootComponentGroup Q H S a,
      (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val).Nonempty)
    (i : Fin 2) {z : InteriorNode (compatibleWhitneyMeshDepth H (a+1))}
    (hz : rootGroupNodalCorrection Q H S a hfin hne i z ≠ 0) :
    ∃ C : rootComponentGroup Q H S a, z ∈ componentMeshNodes Q _ C.val := by
  classical
  by_contra! hn
  exact hz (root_group_nodal_off_components Q H S a hfin hne i hn)

end
end ASDExplicitGamma.Inverse
