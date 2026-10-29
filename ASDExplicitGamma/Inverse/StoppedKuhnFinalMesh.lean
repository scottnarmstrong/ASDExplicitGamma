module

public import ASDExplicitGamma.Inverse.StoppedKuhnSupport

/-! The literal final conforming Kuhn mesh in each actual Whitney cell. It
refines both possible source groups and uses at most two generations. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

def finalWhitneyKuhnCells (Q : TriadicCube 2) (H n : ℕ) (P : TriadicCube 2) :
    Finset (KuhnCell 2) :=
  triadicSimplexPartition P (Q.scale-(compatibleWhitneyMeshDepth H (n+1):ℤ))

theorem final_whitney_kuhn_depth_range (Q : TriadicCube 2) (H n : ℕ)
    {P : TriadicCube 2} (hP : P ∈ whitneyRootLayer Q H n) :
    Q.scale-(compatibleWhitneyMeshDepth H (n+1):ℤ) ≤ P.scale ∧
      P.scale ≤ Q.scale-(compatibleWhitneyMeshDepth H (n+1):ℤ)+2 := by
  have hs := root_whitney_layer_scale Q H n hP
  have hp := whitney_profile_step H n
  unfold compatibleWhitneyMeshDepth
  omega

theorem final_kuhn_root_mem (Q : TriadicCube 2) (H n : ℕ)
    {P : TriadicCube 2} (hP : P ∈ whitneyRootLayer Q H n)
    {U : KuhnCell 2} (hU : U ∈ finalWhitneyKuhnCells Q H n P) :
    U ∈ rootKuhnMesh Q (compatibleWhitneyMeshDepth H (n+1)) := by
  let d := compatibleWhitneyMeshDepth H n
  let D := compatibleWhitneyMeshDepth H (n+1)
  have hs : P.scale=Q.scale-(d:ℤ) := by
    have hh := root_whitney_layer_scale Q H n hP
    unfold d compatibleWhitneyMeshDepth
    omega
  have hd : d ≤ D := by
    have hh := whitney_profile_step H n
    unfold d D compatibleWhitneyMeshDepth
    omega
  have hUd : U.supportCube ∈ descendantsAtDepth P (D-d) := by
    change U ∈ triadicSimplexPartition P (Q.scale-(D:ℤ)) at hU
    rw [mem_triadicSimplexPartition_iff,descendantsAtScale_eq_descendantsAtDepth P (by omega)] at hU
    have hc : (P.scale-(Q.scale-(D:ℤ))).toNat=D-d := by omega
    simpa only [hc] using hU
  have hroot := mem_descendantsAtDepth_add (root_whitney_layer_descendants Q H n hP) hUd
  have he : n+whitneyProfile H n+(D-d)=D := by change d+(D-d)=D; omega
  rw [he] at hroot
  change U ∈ triadicSimplexPartition Q (Q.scale-(D:ℤ))
  rw [mem_triadicSimplexPartition_iff,descendantsAtScale_eq_descendantsAtDepth Q (by omega)]
  simpa only [show (Q.scale-(Q.scale-(D:ℤ))).toNat=D by omega] using hroot

theorem final_kuhn_open_subset (Q : TriadicCube 2) (H n : ℕ)
    {P : TriadicCube 2} (hP : P ∈ whitneyRootLayer Q H n)
    {U : KuhnCell 2} (hU : U ∈ finalWhitneyKuhnCells Q H n P) :
    U.openCarrier ⊆ openCubeSet P := by
  have hscale := (final_whitney_kuhn_depth_range Q H n hP).1
  rw [finalWhitneyKuhnCells,mem_triadicSimplexPartition_iff,
    descendantsAtScale_eq_descendantsAtDepth P hscale] at hU
  exact U.openCarrier_subset_openCubeSet.trans (openCubeSet_subset_of_mem_descendantsAtDepth hU)

/-- Every fine simplex of the final mesh lies in one simplex of the preceding
source group. This is the exact cross-scale compatibility needed by the sum. -/
theorem final_kuhn_previous_parent (Q : TriadicCube 2) (H n : ℕ)
    {P : TriadicCube 2} (hP : P ∈ whitneyRootLayer Q H n)
    {U : KuhnCell 2} (hU : U ∈ finalWhitneyKuhnCells Q H n P) :
    ∃ V ∈ rootKuhnMesh Q (compatibleWhitneyMeshDepth H n), U.openCarrier ⊆ V.openCarrier := by
  have hp := whitney_profile_step H n
  exact triadicSimplexPartition_refines_openCarrier Q (by omega)
    (by unfold compatibleWhitneyMeshDepth; omega) (final_kuhn_root_mem Q H n hP hU)

end
end ASDExplicitGamma.Inverse
