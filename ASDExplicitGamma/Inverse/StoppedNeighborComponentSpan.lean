module

public import ASDExplicitGamma.Inverse.StoppedCanonicalComponents
public import ASDExplicitGamma.Inverse.StoppedComponentSpan
public import ASDExplicitGamma.Inverse.StoppedDiameterCharge

/-! The actual component lift supplies the physical Z span at every cell
of its whole closure-touching neighborhood. No lifted-cluster premise is kept. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- Actual stopped component nodes have the exact physical Z span at every
neighboring source cell. The witness T is that current cell's genuine
coarser-mesh ancestor; its resolution differs by at most two generations. -/
theorem stopped_neighbor_component_span (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (R : TriadicCube 2) (hR : R ∈ S)
    (P : TriadicCube 2) (hP : P ∈ rootWhitneyNeighborhood Q H (badComponent S R)) :
    let C := badComponent S R
    let a := rootComponentLeastLayer Q H C
    let base := a+whitneyProfile H a
    let F := q3PlanarMarks M (Q.scale-base) τ η
    ∃ T, RootWhitneyLift Q base P T ∧
      ∀ (_hfinite : diameterField F ω (fineBlockIndex T.index) ≠ ∞),
        1 ≤ realDiameterField F (fineBlockIndex T.index) ω ∧
        ∀ (J : ℕ) (hne : (componentMeshNodes Q J C).Nonempty) (i : Fin 2),
        componentCoordinateMax Q J (componentMeshNodes Q J C) hne i-
          componentCoordinateMin Q J (componentMeshNodes Q J C) hne i ≤
          2*(3:ℝ)^40*realDiameterField F (fineBlockIndex T.index) ω*(3:ℝ)^(Q.scale-(base:ℤ)) := by
  let C := badComponent S R
  let a := rootComponentLeastLayer Q H C
  let base := a+whitneyProfile H a
  let F := q3PlanarMarks M (Q.scale-base) τ η
  let O := fineOccupied F ω
  have hg := stopped_component_lifted_paths M Q H hH τ η ω hgood S hS hbad R hR
  change (∃ B, B ∈ descendantsAtDepth Q base ∧ ∃ hB : B.index ∈ O,
    ∀ V ∈ C, ∃ A, RootWhitneyLift Q base V A ∧ ∃ hA : A.index ∈ O,
      (fineGraph.induce O).Reachable ⟨B.index,hB⟩ ⟨A.index,hA⟩) ∧
    (∀ D ∈ rootWhitneyNeighborhood Q H C,
      D ∈ whitneyRootLayer Q H a ∨ D ∈ whitneyRootLayer Q H (a+1)) at hg
  obtain ⟨⟨B,hBroot,hB,hpaths⟩,htwo⟩ := hg
  obtain ⟨n,hn,hnP⟩ : ∃ n, (n=a ∨ n=a+1) ∧ P ∈ whitneyRootLayer Q H n := by
    rcases htwo P hP with hp | hp
    · exact ⟨a,Or.inl rfl,hp⟩
    · exact ⟨a+1,Or.inr rfl,hp⟩
  obtain ⟨T,hPT⟩ := root_whitney_two_layer_lift Q H a n (by omega) (by omega) hnP
  obtain ⟨V,hVC,htPV⟩ := hP.2
  obtain ⟨A0,hVA0,hA0,hconn0⟩ := hpaths V hVC
  have hstep := root_whitney_lifts_touch_indices hPT hVA0 htPV
  have hnear : ∀ d, |fineBlockIndex A0.index d-fineBlockIndex T.index d| ≤ 2 := by
    intro d
    exact (fine_block_index_neighbor T.index A0.index (fun k => (hstep k).trans (by norm_num)) d).trans (by norm_num)
  have hlift : ∀ W ∈ C, ∃ A : TriadicCube 2, ∃ n : ℕ,
      W ∈ descendantsAtDepth A n ∧ A.scale=Q.scale-(base:ℤ) ∧
        fineBlockIndex A.index ∈ clusterSites F ω (fineBlockIndex A0.index) := by
    intro W hW
    obtain ⟨A,hWA,hA,hconn⟩ := hpaths W hW
    obtain ⟨r,hr,hWAr⟩ := hWA.2
    have hc := hconn0.symm.trans hconn
    have hcb := fine_reachable_blocks (F := O) (O := markedOccupied F ω) (fun _ hx => hx) hc
    exact ⟨A,r,hWAr,scale_eq_sub_of_mem_descendantsAtDepth hWA.1,⟨hA0,hA,hcb⟩⟩
  refine ⟨T,hPT,?_⟩
  intro hfinite
  refine ⟨real_diameter_one_of_near_occupied F ω (fineBlockIndex T.index)
    (fineBlockIndex A0.index) hnear hfinite hA0,?_⟩
  intro J hne i
  exact component_mesh_coordinate_span F ω (Q.scale-base) (fineBlockIndex T.index)
    (fineBlockIndex A0.index) hnear hfinite Q J C hne hlift i

end
end ASDExplicitGamma.Inverse
