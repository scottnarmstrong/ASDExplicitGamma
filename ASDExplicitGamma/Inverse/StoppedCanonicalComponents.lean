module

public import ASDExplicitGamma.Inverse.StoppedRootWhitneyComponents

/-! Canonical least layers and full lifted paths of actual stopped
components, retained for physical diameter and common-mesh assembly. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- The least layer of the entire closure-touching component neighborhood. -/
def rootComponentLeastLayer (Q : TriadicCube 2) (H : ℕ) (C : Set (TriadicCube 2)) : ℕ :=
  sInf {n | ∃ D ∈ rootWhitneyNeighborhood Q H C, D ∈ whitneyRootLayer Q H n}

theorem root_component_least_layer_le (Q : TriadicCube 2) (H : ℕ) (C : Set (TriadicCube 2))
    {n : ℕ} {D : TriadicCube 2} (hD : D ∈ rootWhitneyNeighborhood Q H C)
    (hn : D ∈ whitneyRootLayer Q H n) : rootComponentLeastLayer Q H C ≤ n :=
  Nat.sInf_le ⟨D,hD,hn⟩

theorem root_component_least_layer_mem (Q : TriadicCube 2) (H : ℕ) (C : Set (TriadicCube 2))
    (hne : C.Nonempty) (hC : C ⊆ whitneyRootPartition Q H) :
    ∃ D ∈ rootWhitneyNeighborhood Q H C,
      D ∈ whitneyRootLayer Q H (rootComponentLeastLayer Q H C) := by
  obtain ⟨V,hV⟩ := hne
  obtain ⟨n,hn⟩ := (root_partition_iff_layer Q H V).mp (hC hV)
  exact Nat.sInf_mem (show {n | ∃ D ∈ rootWhitneyNeighborhood Q H C,
    D ∈ whitneyRootLayer Q H n}.Nonempty from ⟨n,V,⟨hC hV,V,hV,cubeTouch_refl V⟩,hn⟩)

/-- Full lifted fine paths of the actual component are retained after the
stopped-chain argument. The canonical least layer uses the whole neighborhood
and supplies exactly the same old-frame mark family to every lifted cell. -/
theorem stopped_component_lifted_paths (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (R : TriadicCube 2) (hR : R ∈ S) :
    let C := badComponent S R
    let a := rootComponentLeastLayer Q H C
    let base := a+whitneyProfile H a
    let O := fineOccupied (q3PlanarMarks M (Q.scale-base) τ η) ω
    (∃ B : TriadicCube 2, B ∈ descendantsAtDepth Q base ∧ ∃ hB : B.index ∈ O,
      ∀ V ∈ C, ∃ A, RootWhitneyLift Q base V A ∧ ∃ hA : A.index ∈ O,
        (fineGraph.induce O).Reachable ⟨B.index,hB⟩ ⟨A.index,hA⟩) ∧
    ∀ D ∈ rootWhitneyNeighborhood Q H C,
      D ∈ whitneyRootLayer Q H a ∨ D ∈ whitneyRootLayer Q H (a+1) := by
  let C := badComponent S R
  let a := rootComponentLeastLayer Q H C
  have hRmem : R ∈ C := self_mem_badComponent hR
  have hCsub : C ⊆ whitneyRootPartition Q H := fun _ hV => hS hV.1
  obtain ⟨A,hAN,hAa⟩ := root_component_least_layer_mem Q H C ⟨R,hRmem⟩ hCsub
  obtain ⟨U,hUC,htAU⟩ := hAN.2
  have hmin : ∀ V ∈ badComponent S U, ∀ n D,
      D ∈ whitneyRootLayer Q H n → CubeTouch D V → a ≤ n := by
    intro V hV n D hn ht
    have hVC : V ∈ C := ⟨hV.1,hUC.2.trans hV.2⟩
    exact root_component_least_layer_le Q H C
      ⟨(root_partition_iff_layer Q H D).mpr ⟨n,hn⟩,V,hVC,ht⟩ hn
  have hgb := hgood (a+whitneyProfile H a) (by unfold whitneyProfile; omega)
  obtain ⟨B,hUB,hB,hchain⟩ := root_stopped_whitney_chain_confined M Q H a hH τ η ω hgb
    S hS hbad U A hUC.1 hAa htAU hmin
  have hreach (V : TriadicCube 2) (hV : V ∈ C) : BadChain S U V :=
    (badChain_symm hUC.2).trans hV.2
  constructor
  · refine ⟨B,hUB.1,hB,?_⟩
    intro V hV
    obtain ⟨E,hVE,hE,hconn,hbound⟩ := hchain V (hreach V hV)
    exact ⟨E,hVE,hE,hconn⟩
  · intro D hD
    obtain ⟨V,hV,htDV⟩ := hD.2
    obtain ⟨n,hn⟩ := (root_partition_iff_layer Q H D).mp hD.1
    obtain ⟨E,hVE,hE,hconn,hbound⟩ := hchain V (hreach V hV)
    have hl : a ≤ n := root_component_least_layer_le Q H C hD hn
    have hu := hbound n D hn htDV
    rcases (show n=a ∨ n=a+1 by omega) with rfl | rfl
    · exact Or.inl hn
    · exact Or.inr hn

end
end ASDExplicitGamma.Inverse
