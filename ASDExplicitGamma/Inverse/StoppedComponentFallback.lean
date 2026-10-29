module

public import ASDExplicitGamma.Inverse.StoppedCanonicalComponents
public import ASDExplicitGamma.Inverse.StoppedLiftPointDistance

/-! Source deterministic fallback diameters for whole stopped components.
These are physical bounds used to establish H1 summability before response
comparison, independently of the random-density moment estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- Every pair of points in the actual closed component has the physical
stopped-diameter fallback, with its one total fine-parent width. -/
theorem stopped_component_closed_point_fallback (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V) (R : TriadicCube 2) (hR : R ∈ S)
    {U V : TriadicCube 2} (hU : U ∈ badComponent S R) (hV : V ∈ badComponent S R)
    {p q : Vec 2} (hp : p ∈ Metric.closedBall (cubeCenter U) (cubeRadius U))
    (hq : q ∈ Metric.closedBall (cubeCenter V) (cubeRadius V)) :
    let a := rootComponentLeastLayer Q H (badComponent S R)
    let base := a+whitneyProfile H a
    ‖p-q‖ ≤ ((3:ℝ)^((base:ℝ)/4)+1)*(3:ℝ)^(Q.scale-(base:ℤ)) := by
  let C := badComponent S R
  let a := rootComponentLeastLayer Q H C
  let base := a+whitneyProfile H a
  let F := q3PlanarMarks M (Q.scale-base) τ η
  let O := fineOccupied F ω
  have hg := (stopped_component_lifted_paths M Q H hH τ η ω hgood S hS hbad R hR).1
  change ∃ B, B ∈ descendantsAtDepth Q base ∧ ∃ hB : B.index ∈ O,
    ∀ V ∈ C, ∃ A, RootWhitneyLift Q base V A ∧ ∃ hA : A.index ∈ O,
      (fineGraph.induce O).Reachable ⟨B.index,hB⟩ ⟨A.index,hA⟩ at hg
  obtain ⟨B,hBroot,hB,hpaths⟩ := hg
  obtain ⟨A0,hUA0,hA0,hconn0⟩ := hpaths U hU
  obtain ⟨A1,hVA1,hA1,hconn1⟩ := hpaths V hV
  have hbase : 333 ≤ base := by dsimp only [base,whitneyProfile]; omega
  have hgb := hgood base (by dsimp only [base,whitneyProfile]; omega)
  have hd : ∀ d, (|A1.index d-A0.index d|:ℝ) ≤ (3:ℝ)^((base:ℝ)/4) := by
    intro d
    exact (successful_separation_fine_distance F ω Q base hbase hgb hUA0.1 rfl
      (hconn0.symm.trans hconn1) d).le
  exact root_lift_closed_point_distance hUA0 hVA1 hp hq _ (by positivity) hd

/-- Measured from any cell in the minimum neighborhood layer, every actual
component point costs only one further fine side for the touching endpoints. -/
theorem stopped_component_min_cell_distance (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V) (R : TriadicCube 2) (hR : R ∈ S)
    {D : TriadicCube 2} (hD : D ∈ rootWhitneyNeighborhood Q H (badComponent S R))
    (hnD : D ∈ whitneyRootLayer Q H (rootComponentLeastLayer Q H (badComponent S R)))
    {V : TriadicCube 2} (hV : V ∈ badComponent S R) {p : Vec 2}
    (hp : p ∈ Metric.closedBall (cubeCenter V) (cubeRadius V)) :
    let a := rootComponentLeastLayer Q H (badComponent S R)
    let base := a+whitneyProfile H a
    ‖cubeCenter D-p‖ ≤ ((3:ℝ)^((base:ℝ)/4)+2)*(3:ℝ)^(Q.scale-(base:ℤ)) := by
  let C := badComponent S R
  let a := rootComponentLeastLayer Q H C
  let base := a+whitneyProfile H a
  let side : ℝ := (3:ℝ)^(Q.scale-(base:ℤ))
  obtain ⟨U,hUC,htDU⟩ := hD.2
  have ht := (stopped_component_lifted_paths M Q H hH τ η ω hgood S hS hbad R hR).2
  have hUN : U ∈ rootWhitneyNeighborhood Q H C := ⟨hS hUC.1,U,hUC,cubeTouch_refl U⟩
  obtain ⟨n,hn,hnU⟩ : ∃ n, (n=a ∨ n=a+1) ∧ U ∈ whitneyRootLayer Q H n := by
    rcases ht U hUN with hu | hu
    · exact ⟨a,Or.inl rfl,hu⟩
    · exact ⟨a+1,Or.inr rfl,hu⟩
  have hDr : cubeRadius D ≤ side/2 := root_whitney_layer_radius_le Q H a a le_rfl hnD
  have hUr : cubeRadius U ≤ side/2 := root_whitney_layer_radius_le Q H a n (by omega) hnU
  have hDU : ‖cubeCenter D-cubeCenter U‖ ≤ side := by
    have hh := norm_cubeCenter_sub_le_of_cubeTouch htDU
    linarith only [hh,hDr,hUr]
  have hUp := stopped_component_closed_point_fallback M Q H hH τ η ω hgood S hS hbad R hR hUC hV
    (Metric.mem_closedBall_self (cubeRadius_nonneg U)) hp
  have htri := norm_sub_le_norm_sub_add_norm_sub (cubeCenter D) (cubeCenter U) p
  change ‖cubeCenter D-p‖ ≤ ((3:ℝ)^((base:ℝ)/4)+2)*side
  change ‖cubeCenter U-p‖ ≤ ((3:ℝ)^((base:ℝ)/4)+1)*side at hUp
  linarith only [hDU,hUp,htri]

end
end ASDExplicitGamma.Inverse
