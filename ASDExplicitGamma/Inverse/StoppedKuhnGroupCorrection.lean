module

public import ASDExplicitGamma.Inverse.StoppedKuhnContinuity
public import ASDExplicitGamma.Inverse.StoppedGroupLayerSupport

/-! Actual finite-Kuhn realization of the stopped midpoint groups. Compact
support, continuity, weak derivatives and zero trace are all derived from
the stopped source geometry; no geometric conclusion is left as a premise. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Affine Algsuperdiff.Section3.Provider.Whitney
noncomputable section

theorem stopped_group_closed_stars_interior (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (a : ℕ) (hfin : (rootComponentGroup Q H S a).Finite)
    (hne : ∀ C : rootComponentGroup Q H S a,
      (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val).Nonempty)
    (i : Fin 2) :
    nodalClosedStars Q (compatibleWhitneyMeshDepth H (a+1))
      (rootGroupNodalCorrection Q H S a hfin hne i) ⊆ openCubeSet Q := by
  intro x hx
  obtain ⟨z,hz,hxz⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨C,hCz⟩ := root_group_nodal_nonzero_component Q H S a hfin hne i hz
  obtain ⟨V,hVC,hzV⟩ := (component_mesh_nodes_mem Q _ C.val z).mp hCz
  obtain ⟨R,hR,he⟩ := C.property.1
  have hVS : V ∈ S := by
    have hh : V ∈ badComponent S R := by rwa [← he]
    exact hh.1
  have hl := stopped_group_neighborhood_layers M Q H hH τ η ω hgood S hS hbad a C
    (show V ∈ rootWhitneyNeighborhood Q H C.val from ⟨hS hVS,V,hVC,cubeTouch_refl V⟩)
  have hnear (k : Fin 2) : |x k-diagInteriorVertex Q (compatibleWhitneyMeshDepth H (a+1)) z k| ≤
      diagMeshRadius Q (compatibleWhitneyMeshDepth H (a+1)) := by
    have hh := norm_le_pi_norm (x-diagInteriorVertex Q _ z) k
    have hc : |x k-diagInteriorVertex Q (compatibleWhitneyMeshDepth H (a+1)) z k| ≤
        ‖x-diagInteriorVertex Q _ z‖ := by simpa only [Pi.sub_apply,Real.norm_eq_abs] using hh
    exact hc.trans (Metric.mem_closedBall.mp hxz)
  rcases hl with hl | hl
  · apply root_whitney_closed_star_interior Q H a _ hl _ hzV hnear
    have hm : whitneyProfile H a ≤ whitneyProfile H (a+1) := whitney_profile_mono H (by omega)
    unfold compatibleWhitneyMeshDepth
    omega
  · exact root_whitney_closed_star_interior Q H (a+1) _ hl le_rfl hzV hnear

variable (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (a : ℕ) (hfin : (rootComponentGroup Q H S a).Finite)
    (hne : ∀ C : rootComponentGroup Q H S a,
      (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val).Nonempty)

/-- The actual source group with its prescribed bounding-box midpoint datum,
interpolated affinely on the literal Kuhn simplices of its own common mesh. -/
def rootKuhnGroupCorrection (i : Fin 2) : H1Function (openCubeSet Q) := by
  let J := compatibleWhitneyMeshDepth H (a+1)
  let b := rootGroupNodalCorrection Q H S a hfin hne i
  have hs := stopped_group_closed_stars_interior M Q H hH τ η ω hgood S hS hbad a hfin hne i
  have hc := kuhn_nodal_extension_continuous Q J b hs
  have hcompact : HasCompactSupport (kuhnNodalExtension Q J b) :=
    HasCompactSupport.intro (nodal_closed_stars_compact Q J b)
      (fun _ hx => kuhn_nodal_extension_zero_off_stars Q J b hx)
  exact finiteKuhnH1 Q (rootKuhnMesh Q J) (diagSynthesisH1Linear Q J b).toFun
    (fun T hT => root_kuhn_mesh_scale Q J hT) hc hcompact

theorem root_kuhn_group_correction_memH10 (i : Fin 2) :
    MemH10 (openCubeSet Q) (rootKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad a hfin hne i).toFun := by
  let J := compatibleWhitneyMeshDepth H (a+1)
  let b := rootGroupNodalCorrection Q H S a hfin hne i
  have hs := stopped_group_closed_stars_interior M Q H hH τ η ω hgood S hS hbad a hfin hne i
  change MemH10 (openCubeSet Q) (kuhnNodalExtension Q J b)
  exact finite_kuhn_h1_memH10 Q (rootKuhnMesh Q J)
    (diagSynthesisH1Linear Q J b).toFun
    (fun T hT => root_kuhn_mesh_scale Q J hT)
    (kuhn_nodal_extension_continuous Q J b hs) (nodalClosedStars Q J b)
    (nodal_closed_stars_compact Q J b) hs
    (fun _ hx => kuhn_nodal_extension_zero_off_stars Q J b hx)

end
end ASDExplicitGamma.Inverse
