module

public import ASDExplicitGamma.Inverse.StoppedKuhnSupport

/-! Continuity of the literal finite root-mesh interpolation follows from
its compact support strictly inside the root. No face matching premise is
needed: the single-scale Kuhn gluing theorem proves it. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Filter Topology ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Provider.Affine Algsuperdiff.Section3.Provider.Whitney
noncomputable section

theorem root_kuhn_closed_cover (Q : TriadicCube 2) (j : ℕ) {x : Vec 2}
    (hx : x ∈ cubeSet Q) : ∃ T ∈ rootKuhnMesh Q j, x ∈ T.closedCarrier := by
  rw [cubeSet_eq_iUnion_triadicSimplexPartition Q (by omega : Q.scale-(j:ℤ) ≤ Q.scale)] at hx
  obtain ⟨T,hT,hxT⟩ := Set.mem_iUnion₂.mp hx
  exact ⟨T,hT,T.carrier_subset_closedCarrier hxT⟩

/-- The fixed nodal interpolation is continuous once its actual closed stars
are shown to lie inside the root. The internal face equations are derived. -/
theorem kuhn_nodal_extension_continuous (Q : TriadicCube 2) (j : ℕ)
    (b : InteriorNode j → ℝ) (hstars : nodalClosedStars Q j b ⊆ openCubeSet Q) :
    Continuous (kuhnNodalExtension Q j b) := by
  let cells := rootKuhnMesh Q j
  let datum := (diagSynthesisH1Linear Q j b).toFun
  let K := nodalClosedStars Q j b
  have hK := nodal_closed_stars_compact Q j b
  have hzero : ∀ x, x ∉ K → kuhnNodalExtension Q j b x=0 :=
    fun _ hx => kuhn_nodal_extension_zero_off_stars Q j b hx
  have hscale := fun T hT => root_kuhn_mesh_scale Q j (T := T) hT
  have hcont := continuousOn_gluedKuhnAffine hscale datum
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxU : x ∈ openCubeSet Q
  · have hnhds : (⋃ T ∈ (cells : Set (KuhnCell 2)), T.closedCarrier) ∈ 𝓝 x := by
      apply Filter.mem_of_superset ((isOpen_openCubeSet Q).mem_nhds hxU)
      intro y hy
      obtain ⟨T,hT,hyT⟩ := root_kuhn_closed_cover Q j ((openCubeSet_subset_cubeSet Q) hy)
      exact Set.mem_iUnion₂.mpr ⟨T,hT,hyT⟩
    have hxin : x ∈ ⋃ T ∈ (cells : Set (KuhnCell 2)), T.closedCarrier := by
      obtain ⟨T,hT,hxT⟩ := root_kuhn_closed_cover Q j ((openCubeSet_subset_cubeSet Q) hxU)
      exact Set.mem_iUnion₂.mpr ⟨T,hT,hxT⟩
    apply ((hcont x hxin).continuousAt hnhds).congr_of_eventuallyEq
    filter_upwards [(isOpen_openCubeSet Q).mem_nhds hxU] with y hy
    obtain ⟨T,hT,hyT⟩ := root_kuhn_closed_cover Q j ((openCubeSet_subset_cubeSet Q) hy)
    change zeroExtendedKuhnAffine cells datum y=gluedKuhnAffine cells datum y
    rw [zeroExtendedKuhnAffine,ite_eq_left ⟨T,hT,hyT⟩]
  · have hxK : x ∉ K := fun hxK => hxU (hstars hxK)
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.eventually_mem hxK] with y hy
    exact hzero y hy

end
end ASDExplicitGamma.Inverse
