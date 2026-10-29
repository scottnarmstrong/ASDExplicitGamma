module

public import ASDExplicitGamma.Inverse.HybridCells

/-! Disjointness and null-set exhaustion for the actual hybrid dissection. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Whitney
open Algsuperdiff.Section3.Provider.Multiscale
noncomputable section

/-- Hybrid cells with distinct Whitney parents are disjoint. -/
theorem hybrid_disjoint_of_parent_ne {Q : TriadicCube 2} {H : ℕ} {S : Set (TriadicCube 2)}
    (i j : HybridCell Q H S) (hne : (hybridParent i).2.val ≠ (hybridParent j).2.val) :
    Disjoint (hybridDomain i:Set (Vec 2)) (hybridDomain j:Set (Vec 2)) := by
  have hi := (root_partition_iff_layer Q H _).mpr ⟨(hybridParent i).1,(hybridParent i).2.property⟩
  have hj := (root_partition_iff_layer Q H _).mpr ⟨(hybridParent j).1,(hybridParent j).2.property⟩
  exact (whitney_root_partition_disjoint Q H hi hj hne).mono
    ((hybrid_domain_subset_parent i).trans (openCubeSet_subset_cubeSet _))
    ((hybrid_domain_subset_parent j).trans (openCubeSet_subset_cubeSet _))

/-- All actual hybrid interiors are pairwise disjoint, including interfaces
between whole identity cubes and active final simplices. -/
theorem hybrid_domains_disjoint (Q : TriadicCube 2) (H : ℕ) (S : Set (TriadicCube 2)) :
    Pairwise (fun i j : HybridCell Q H S => Disjoint (hybridDomain i:Set (Vec 2))
      (hybridDomain j:Set (Vec 2))) := by
  classical
  have hIA (i : HybridIdentityCell Q H S) (j : HybridActiveCell Q H S) :
      Disjoint (hybridDomain (.inl i):Set (Vec 2)) (hybridDomain (.inr j):Set (Vec 2)) := by
    by_cases he : i.val.2.val=j.1.val.2.val
    · have hh := whitney_indexed_cube_injective Q H he
      have hg : ∀ V ∈ S, ¬ CubeTouch j.1.val.2.val V := by rw [← hh]; exact i.property
      exact (j.1.property hg).elim
    · exact hybrid_disjoint_of_parent_ne (.inl i) (.inr j) he
  intro i j hne
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      apply hybrid_disjoint_of_parent_ne (.inl i) (.inl j)
      intro he
      have hh : i=j := Subtype.ext (whitney_indexed_cube_injective Q H he)
      exact hne (congrArg Sum.inl hh)
    | inr j => exact hIA i j
  | inr i =>
    cases j with
    | inl j => exact (hIA j i).symm
    | inr j =>
      by_cases he : i.1.val.2.val=j.1.val.2.val
      · have hh : i.1=j.1 := Subtype.ext (whitney_indexed_cube_injective Q H he)
        rcases i with ⟨i,T⟩
        rcases j with ⟨j,U⟩
        dsimp only at hh
        cases hh
        have hTU : T.val ≠ U.val := by
          intro heq
          have hh : T=U := Subtype.ext heq
          subst U
          exact hne rfl
        exact triadicSimplexPartition_openCarrier_pairwiseDisjoint i.val.2.val
          (Q.scale-(compatibleWhitneyMeshDepth H (i.val.1+1):ℤ)) T.property U.property hTU
      · exact hybrid_disjoint_of_parent_ne (.inr i) (.inr j) he

/-- The literal hybrid interiors exhaust the root up to a null set. -/
theorem hybrid_domains_cover (Q : TriadicCube 2) (H : ℕ) (S : Set (TriadicCube 2)) :
    volume (openCubeSet Q \ ⋃ i : HybridCell Q H S, (hybridDomain i:Set (Vec 2)))=0 := by
  classical
  have hT (T : KuhnCell 2) : T.carrier =ᵐ[volume] T.openCarrier := by
    apply ae_eq_set.mpr
    exact ⟨volume_carrier_diff_openCarrier T,by
      rw [Set.sdiff_eq_empty.mpr T.openCarrier_subset_carrier,measure_empty]⟩
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_all_iff.mpr hT,ae_all_iff.mpr (fun P : TriadicCube 2 => cubeSet_ae_eq_openCubeSet P)] with x hxT hxP
  rintro ⟨hxQ,hxnot⟩
  rw [whitney_root_partition_cover] at hxQ
  obtain ⟨P,hP,hxPcube⟩ := Set.mem_iUnion₂.mp hxQ
  obtain ⟨n,hn⟩ := (root_partition_iff_layer Q H P).mp hP
  let i : WhitneyIndexedCell Q H := ⟨n,⟨P,hn⟩⟩
  by_cases hi : ∀ V ∈ S, ¬ CubeTouch P V
  · apply hxnot
    exact Set.mem_iUnion.mpr ⟨.inl ⟨i,hi⟩,(hxP P).mp hxPcube⟩
  · have hdepth := (final_whitney_kuhn_depth_range Q H n hn).1
    have hcover := cubeSet_eq_iUnion_triadicSimplexPartition P hdepth
    rw [hcover] at hxPcube
    obtain ⟨T,hT,hxTc⟩ := Set.mem_iUnion₂.mp hxPcube
    have hcell : T ∈ finalWhitneyKuhnCells Q H n P := hT
    apply hxnot
    exact Set.mem_iUnion.mpr ⟨.inr ⟨⟨i,hi⟩,⟨T,hcell⟩⟩,(hxT T).mp hxTc⟩

end
end ASDExplicitGamma.Inverse
