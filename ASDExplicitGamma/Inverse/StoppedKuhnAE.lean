module

public import ASDExplicitGamma.Inverse.StoppedKuhnSupport

/-! A single spatial null set removes the faces of a finite root Kuhn mesh.
The resulting interior cover identifies the literal constant weak slopes. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3.Provider.Whitney Algsuperdiff.Section3.Provider.Multiscale
noncomputable section

theorem root_kuhn_open_cover_null (Q : TriadicCube 2) (j : ℕ) :
    volume (openCubeSet Q \ ⋃ T ∈ (rootKuhnMesh Q j : Set (KuhnCell 2)), T.openCarrier)=0 := by
  have hs : openCubeSet Q \ ⋃ T ∈ (rootKuhnMesh Q j : Set (KuhnCell 2)), T.openCarrier ⊆
      ⋃ T ∈ (rootKuhnMesh Q j : Set (KuhnCell 2)), T.carrier \ T.openCarrier := by
    intro x hx
    have hxQ := (openCubeSet_subset_cubeSet Q) hx.1
    rw [cubeSet_eq_iUnion_triadicSimplexPartition Q (by omega : Q.scale-(j:ℤ) ≤ Q.scale)] at hxQ
    obtain ⟨T,hT,hxT⟩ := Set.mem_iUnion₂.mp hxQ
    refine Set.mem_iUnion₂.mpr ⟨T,hT,hxT,?_⟩
    exact fun ho => hx.2 (Set.mem_iUnion₂.mpr ⟨T,hT,ho⟩)
  apply measure_mono_null hs
  apply (measure_biUnion_null_iff (Set.to_countable _)).mpr
  intro T _
  exact volume_carrier_diff_openCarrier T

/-- Almost every point of an arbitrary translated root belongs to an open
simplex of its actual finite triadic Kuhn mesh. -/
theorem root_kuhn_ae_open_cover (Q : TriadicCube 2) (j : ℕ) :
    ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      ∃ T ∈ rootKuhnMesh Q j, x ∈ T.openCarrier := by
  have hn := (measure_eq_zero_iff_ae_notMem).mp (root_kuhn_open_cover_null Q j)
  filter_upwards [ae_restrict_of_ae hn,ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx hxQ
  by_contra he
  apply hx
  refine ⟨hxQ,?_⟩
  intro hi
  obtain ⟨T,hT,hxT⟩ := Set.mem_iUnion₂.mp hi
  exact he ⟨T,hT,hxT⟩

end
end ASDExplicitGamma.Inverse
