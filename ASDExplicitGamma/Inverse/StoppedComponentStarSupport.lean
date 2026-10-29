module

public import ASDExplicitGamma.Inverse.StoppedComponentFallback
public import ASDExplicitGamma.Inverse.StoppedComponentMeshNodes
public import ASDExplicitGamma.Inverse.StoppedMeshStar

/-! Source tensor stars stay in the actual closure-touching component
neighborhood. The stopped macro-layer contradiction is used before mesh
nesting, so no extra collar is inserted. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney ASDExplicitGamma.Triadic
noncomputable section

theorem diag_mesh_radius_eq_zpow (Q : TriadicCube 2) (j : ℕ) :
    diagMeshRadius Q j = (3:ℝ)^(Q.scale-(j:ℤ)) := by
  unfold diagMeshRadius cubeScaleFactor
  rw [zpow_sub₀ (by norm_num : (3:ℝ) ≠ 0),zpow_natCast]

/-- The entire mesh star of an actual component node can meet an interior
Whitney cell only inside that component's whole touching neighborhood. -/
theorem stopped_component_node_star_in_neighborhood (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V) (R : TriadicCube 2) (hR : R ∈ S) :
    let C := badComponent S R
    let a := rootComponentLeastLayer Q H C
    let J := compatibleWhitneyMeshDepth H (a+1)
    ∀ z ∈ componentMeshNodes Q J C, ∀ n (P : TriadicCube 2),
      P ∈ whitneyRootLayer Q H n → ∀ x ∈ openCubeSet P,
      (∀ k, |x k-diagInteriorVertex Q J z k| ≤ diagMeshRadius Q J) →
        P ∈ rootWhitneyNeighborhood Q H C := by
  let C := badComponent S R
  let a := rootComponentLeastLayer Q H C
  let base := a+whitneyProfile H a
  let J := compatibleWhitneyMeshDepth H (a+1)
  let side : ℝ := (3:ℝ)^(Q.scale-(base:ℤ))
  let clock : ℝ := (3:ℝ)^((base:ℝ)/4)
  dsimp only
  intro z hz n P hP x hx hnear
  obtain ⟨V,hVC,hnodeV⟩ := (component_mesh_nodes_mem Q J C z).mp hz
  have hJ : base ≤ J := by
    have hm : whitneyProfile H a ≤ whitneyProfile H (a+1) :=
      whitney_profile_mono H (show a ≤ a+1 by omega)
    dsimp only [base,J,compatibleWhitneyMeshDepth]
    omega
  have hmesh : diagMeshRadius Q J ≤ side := by
    rw [diag_mesh_radius_eq_zpow]
    apply zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 3)
    omega
  have hn : n ≤ a+1 := by
    by_contra hn
    have han : a+2 ≤ n := by omega
    have hCsub : C ⊆ whitneyRootPartition Q H := fun _ hV => hS hV.1
    obtain ⟨D,hDN,hDa⟩ := root_component_least_layer_mem Q H C ⟨R,self_mem_badComponent hR⟩ hCsub
    have hDnode := stopped_component_min_cell_distance M Q H hH τ η ω hgood S hS hbad R hR
      hDN hDa hVC hnodeV
    change ‖cubeCenter D-diagInteriorVertex Q J z‖ ≤ (clock+2)*side at hDnode
    have hnx : ‖diagInteriorVertex Q J z-x‖ ≤ side := by
      apply le_trans _ hmesh
      apply (pi_norm_le_iff_of_nonneg (diagMeshRadius_pos Q J).le).mpr
      intro k
      simpa only [Pi.sub_apply,Real.norm_eq_abs,abs_sub_comm] using hnear k
    have hPr : cubeRadius P ≤ side/2 := root_whitney_layer_radius_le Q H a n (by omega) hP
    have hxp := cubeSet_subset_closedBall P ((openCubeSet_subset_cubeSet P) hx)
    rw [Metric.mem_closedBall,dist_eq_norm] at hxp
    have hxP : ‖x-cubeCenter P‖ ≤ side/2 := hxp.trans hPr
    have hclock : 1 ≤ clock := Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 3) (by positivity)
    have hside : 0 ≤ side := (zpow_pos (by norm_num) _).le
    have hp := mul_nonneg (show 0 ≤ clock-1 by linarith only [hclock]) hside
    have ht := norm_sub_le_norm_sub_add_norm_sub (cubeCenter D) (diagInteriorVertex Q J z) (cubeCenter P)
    have ht' := norm_sub_le_norm_sub_add_norm_sub (diagInteriorVertex Q J z) x (cubeCenter P)
    have hDP : ‖cubeCenter D-cubeCenter P‖ ≤ 8*clock*side := by
      nlinarith only [hDnode,hnx,hxP,ht,ht',hp,hside]
    have hsep := root_whitney_layer_gap Q H a n han hDa hP
    have hgate := whitney_separation_gate Q.scale H a (by omega)
    change 4*clock*side < (1/3:ℝ)*(3:ℝ)^(Q.scale-(a:ℤ)) at hgate
    linarith only [hsep,hgate,hDP]
  have hdepth : n+whitneyProfile H n ≤ J := by
    have hm := whitney_profile_mono H hn
    dsimp only [J,compatibleWhitneyMeshDepth]
    omega
  have hnodeP := common_mesh_star_node_in_cell Q (root_whitney_layer_descendants Q H n hP)
    hdepth z hx hnear
  exact ⟨(root_partition_iff_layer Q H P).mpr ⟨n,hP⟩,V,hVC,⟨_,hnodeP,hnodeV⟩⟩

end
end ASDExplicitGamma.Inverse
