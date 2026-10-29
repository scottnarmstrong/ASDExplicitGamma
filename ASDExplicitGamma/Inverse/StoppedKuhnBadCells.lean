module

public import ASDExplicitGamma.Inverse.StoppedKuhnGroupFields
public import ASDExplicitGamma.Inverse.StoppedKuhnAffineRecovery
public import ASDExplicitGamma.Inverse.StoppedTwoGroupSupport

/-! The actual source bounding-box midpoint is recovered on every bad cell.
The source group's Kuhn correction has slope minus the identity there. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Affine Algsuperdiff.Section3.Provider.Whitney
noncomputable section

variable (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (a : ℕ) (hfin : (rootComponentGroup Q H S a).Finite)
    (hne : ∀ C : rootComponentGroup Q H S a,
      (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val).Nonempty)

include M hH τ η ω hgood hS hbad in
theorem stopped_kuhn_group_bad_vertex_data (i : Fin 2)
    (C : rootComponentGroup Q H S a) (n : ℕ) (V : TriadicCube 2)
    (hVC : V ∈ C.val) (hV : V ∈ whitneyRootLayer Q H n)
    (U : KuhnCell 2) (hU : U ∈ rootKuhnMesh Q (compatibleWhitneyMeshDepth H (a+1)))
    (x : Vec 2) (hxV : x ∈ openCubeSet V) (hxU : x ∈ U.openCarrier) (v : Fin 3) :
    (rootGroupCorrection Q H S a hfin hne i).toFun (U.vertex v)=
      componentMidpoint Q _ (componentMeshNodes Q _ C.val) (hne C) i-U.vertex v i := by
  let J := compatibleWhitneyMeshDepth H (a+1)
  obtain ⟨R,hR,he⟩ := C.property.1
  have hVS : V ∈ S := by
    have hh : V ∈ badComponent S R := by rwa [← he]
    exact hh.1
  have hl := stopped_group_neighborhood_layers M Q H hH τ η ω hgood S hS hbad a C
    (show V ∈ rootWhitneyNeighborhood Q H C.val from ⟨hS hVS,V,hVC,cubeTouch_refl V⟩)
  have hJ : n+whitneyProfile H n ≤ J := by
    rcases hl with hl | hl
    · have heq := root_whitney_layer_unique Q H n a hV hl
      subst n
      have hp : whitneyProfile H a ≤ whitneyProfile H (a+1) := whitney_profile_mono H (by omega)
      unfold J compatibleWhitneyMeshDepth
      omega
    · have heq := root_whitney_layer_unique Q H n (a+1) hV hl
      subst n
      exact le_rfl
  have hnear (d : Fin 2) : |U.vertex v d-x d| ≤ diagMeshRadius Q J := by
    simpa only [abs_sub_comm] using kuhn_closed_point_vertex_near Q J hU (U.openCarrier_subset_closedCarrier hxU) v d
  have hvU : U.vertex v ∈ openCubeSet Q :=
    root_whitney_closed_star_interior Q H n J hV hJ
      (cubeSet_subset_closedBall V ((openCubeSet_subset_cubeSet V) hxV)) hnear
  have hUd : U.supportCube ∈ descendantsAtDepth Q J := by
    change U ∈ rootKuhnMesh Q J at hU
    rw [rootKuhnMesh,mem_triadicSimplexPartition_iff,
      descendantsAtScale_eq_descendantsAtDepth Q (by omega)] at hU
    simpa only [show (Q.scale-(Q.scale-(J:ℤ))).toNat=J by omega] using hU
  obtain ⟨ε,hε⟩ := kuhn_vertex_is_cell_corner U v
  obtain ⟨z,hz⟩ := cell_corner_node_of_mem_open Q hUd ε (by rwa [← hε])
  have hez : diagInteriorVertex Q J z=U.vertex v := hz.trans hε.symm
  have hzV := common_mesh_star_node_in_cell Q (root_whitney_layer_descendants Q H n hV) hJ z hxV
    (fun d => by rw [hez]; simpa only [abs_sub_comm] using hnear d)
  have hzC : z ∈ componentMeshNodes Q J C.val :=
    (component_mesh_nodes_mem Q J C.val z).mpr ⟨V,hVC,hzV⟩
  change (diagSynthesisH1Linear Q J (rootGroupNodalCorrection Q H S a hfin hne i)).toFun (U.vertex v)=_
  rw [← hez,diag_synthesis_at_node,root_group_nodal_on_component Q H S a hfin hne C hzC i]

theorem stopped_kuhn_group_flatten_bad_cell (i : Fin 2)
    (C : rootComponentGroup Q H S a) (n : ℕ) (V : TriadicCube 2)
    (hVC : V ∈ C.val) (hV : V ∈ whitneyRootLayer Q H n)
    (U : KuhnCell 2) (hU : U ∈ rootKuhnMesh Q (compatibleWhitneyMeshDepth H (a+1)))
    (x : Vec 2) (hxV : x ∈ openCubeSet V) (hxU : x ∈ U.openCarrier) :
    (rootKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad a hfin hne i).toFun x=
      componentMidpoint Q _ (componentMeshNodes Q _ C.val) (hne C) i-x i ∧
    ∀ k, (rootKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad a hfin hne i).grad x k= -(basisVec i k) := by
  have hv := stopped_kuhn_group_bad_vertex_data M Q H hH τ η ω hgood S hS hbad a hfin hne i C n V hVC hV U hU x hxV hxU
  have hh := kuhn_midpoint_affine_recovery U (rootGroupCorrection Q H S a hfin hne i).toFun _ i hv
  constructor
  · rw [root_kuhn_group_value_on_simplex M Q H hH τ η ω hgood S hS hbad a hfin hne i hU (U.openCarrier_subset_closedCarrier hxU)]
    exact hh.2 x
  · intro k
    rw [root_kuhn_group_gradient_on_simplex M Q H hH τ η ω hgood S hS hbad a hfin hne i k hU hxU,hh.1]
    rfl

end
end ASDExplicitGamma.Inverse
