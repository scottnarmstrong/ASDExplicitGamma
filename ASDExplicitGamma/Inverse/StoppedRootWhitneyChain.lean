module

public import ASDExplicitGamma.Inverse.StoppedRootWhitneyNeighborhood
public import ASDExplicitGamma.Inverse.StoppedWhitneyChain

/-! The stopped-chain induction establishes two-layer confinement before
lifting the whole component. No component finiteness is assumed. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- Every finite prefix of the actual bad-cell chain lifts on the same
two-generation mesh and has its full touching neighborhood in two layers.
The minimum-layer premise is just the defining property of the least
neighborhood layer, discharged in the component theorem. -/
theorem root_stopped_whitney_chain_confined (M : ABKModel 2) (Q : TriadicCube 2)
    (H a : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-(a+whitneyProfile H a:ℕ)) τ η)
      (a+whitneyProfile H a) (rootBlockStart Q (a+whitneyProfile H a)))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (U A : TriadicCube 2) (hU : U ∈ S) (hA : A ∈ whitneyRootLayer Q H a)
    (htAU : CubeTouch A U)
    (hmin : ∀ V ∈ badComponent S U, ∀ n D, D ∈ whitneyRootLayer Q H n → CubeTouch D V → a ≤ n) :
    ∃ B, RootWhitneyLift Q (a+whitneyProfile H a) U B ∧
      ∃ hB : B.index ∈ fineOccupied (q3PlanarMarks M (Q.scale-(a+whitneyProfile H a:ℕ)) τ η) ω,
      ∀ V, BadChain S U V →
        ∃ C, RootWhitneyLift Q (a+whitneyProfile H a) V C ∧
          ∃ hC : C.index ∈ fineOccupied (q3PlanarMarks M (Q.scale-(a+whitneyProfile H a:ℕ)) τ η) ω,
          (fineGraph.induce (fineOccupied
            (q3PlanarMarks M (Q.scale-(a+whitneyProfile H a:ℕ)) τ η) ω)).Reachable
              ⟨B.index,hB⟩ ⟨C.index,hC⟩ ∧
          ∀ n D, D ∈ whitneyRootLayer Q H n → CubeTouch D V → n ≤ a+1 := by
  obtain ⟨nU,hnU⟩ := (root_partition_iff_layer Q H U).mp (hS hU)
  have hlowU : a ≤ nU := hmin U (self_mem_badComponent hU) nU U hnU (cubeTouch_refl U)
  have huppU : nU ≤ a+1 := (root_whitney_touching_layers Q H a nU hA hnU htAU).2
  obtain ⟨B,hUB⟩ := root_whitney_two_layer_lift Q H a nU hlowU huppU hnU
  have hB := root_whitney_lift_bad_occupied M Q (a+whitneyProfile H a) τ η ω hUB (hbad U hU)
  refine ⟨B,hUB,hB,?_⟩
  intro V hchain
  induction hchain with
  | refl =>
    refine ⟨B,hUB,hB,SimpleGraph.Reachable.rfl,?_⟩
    intro n D hD htDU
    exact root_stopped_chain_neighborhood_layer_le M Q H a hH τ η ω hgood hA htAU htDU.symm
      hUB hUB hB hB SimpleGraph.Reachable.rfl n
      (hmin U (self_mem_badComponent hU) n D hD htDU) hD
  | @tail V' V hchain hstep ih =>
    obtain ⟨C',hV'C',hC',hconn',hprev⟩ := ih
    obtain ⟨hV'S,hVS,ht⟩ := hstep
    have hVC : V ∈ badComponent S U := ⟨hVS,Relation.ReflTransGen.tail hchain ⟨hV'S,hVS,ht⟩⟩
    obtain ⟨nV,hnV⟩ := (root_partition_iff_layer Q H V).mp (hS hVS)
    have hlowV : a ≤ nV := hmin V hVC nV V hnV (cubeTouch_refl V)
    have huppV : nV ≤ a+1 := hprev nV V hnV ht.symm
    obtain ⟨C,hVC⟩ := root_whitney_two_layer_lift Q H a nV hlowV huppV hnV
    have hC := root_whitney_lift_bad_occupied M Q (a+whitneyProfile H a) τ η ω hVC (hbad V hVS)
    have hstepconn := fine_neighbor_reachable
      (x := ⟨C'.index,hC'⟩) (y := ⟨C.index,hC⟩) (root_whitney_lifts_touch_indices hV'C' hVC ht)
    have hconn := hconn'.trans hstepconn
    refine ⟨C,hVC,hC,hconn,?_⟩
    intro n D hD htDV
    exact root_stopped_chain_neighborhood_layer_le M Q H a hH τ η ω hgood hA htAU htDV.symm
      hUB hVC hB hC hconn n (hmin V ‹V ∈ badComponent S U› n D hD htDV) hD

end
end ASDExplicitGamma.Inverse
