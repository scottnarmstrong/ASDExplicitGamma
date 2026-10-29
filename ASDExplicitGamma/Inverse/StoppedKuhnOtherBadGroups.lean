module

public import ASDExplicitGamma.Inverse.StoppedKuhnGroupFields
public import ASDExplicitGamma.Inverse.StoppedTwoGroupSupport

/-! Every other canonical group vanishes on a bad component. The argument
uses actual closed-node intersections, not disjoint component neighborhoods. -/
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

theorem stopped_kuhn_other_group_zero_on_bad_cell (i : Fin 2) (n : ℕ)
    (V : TriadicCube 2) (hVS : V ∈ S) (hV : V ∈ whitneyRootLayer Q H n)
    (ha : a ≠ rootComponentLeastLayer Q H (badComponent S V))
    (x : Vec 2) (hxV : x ∈ openCubeSet V) :
    (rootKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad a hfin hne i).toFun x=0 ∧
      ∀ k, (rootKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad a hfin hne i).grad x k=0 := by
  let J := compatibleWhitneyMeshDepth H (a+1)
  let b := rootGroupNodalCorrection Q H S a hfin hne i
  have hnot : x ∉ nodalClosedStars Q J b := by
    intro hx
    obtain ⟨z,hz,hxz⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨C,hCz⟩ := root_group_nodal_nonzero_component Q H S a hfin hne i hz
    have hnear (k : Fin 2) : |x k-diagInteriorVertex Q J z k| ≤ diagMeshRadius Q J := by
      have hc : |x k-diagInteriorVertex Q J z k| ≤ ‖x-diagInteriorVertex Q J z‖ := by
        simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (x-diagInteriorVertex Q J z) k
      exact hc.trans (Metric.mem_closedBall.mp hxz)
    have hVN := stopped_group_node_star_neighborhood M Q H hH τ η ω hgood S hS hbad a C z hCz n V hV x hxV hnear
    have hl := stopped_group_neighborhood_layers M Q H hH τ η ω hgood S hS hbad a C hVN
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
    have hzV := common_mesh_star_node_in_cell Q (root_whitney_layer_descendants Q H n hV) hJ z hxV hnear
    obtain ⟨W,hWC,hzW⟩ := (component_mesh_nodes_mem Q J C.val z).mp hCz
    obtain ⟨R,hR,he⟩ := C.property.1
    have hWR : W ∈ badComponent S R := by rwa [← he]
    have heRV := bad_components_eq_of_touch S R V hWR (self_mem_badComponent hVS) ⟨_,hzW,hzV⟩
    have heC : C.val=badComponent S V := he.trans heRV
    have hl' : rootComponentLeastLayer Q H (badComponent S V)=a := by rw [← heC]; exact C.property.2
    exact ha hl'.symm
  exact ⟨kuhn_nodal_extension_zero_off_stars Q J b hnot,
    fun k => kuhn_nodal_derivative_zero_off_stars Q J b hnot k⟩

end
end ASDExplicitGamma.Inverse
