module

public import ASDExplicitGamma.Inverse.StoppedKuhnGroupCorrection
public import ASDExplicitGamma.Inverse.StoppedKuhnDerivativeSupport
public import ASDExplicitGamma.Inverse.StoppedKuhnScalarBounds
public import ASDExplicitGamma.Inverse.StoppedGroupFallback

/-! Literal simplex fields and whole-cell support of the actual stopped
Kuhn midpoint groups. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Affine Algsuperdiff.Section3.Provider.Whitney
noncomputable section

variable (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (a : ℕ) (hfin : (rootComponentGroup Q H S a).Finite)
    (hne : ∀ C : rootComponentGroup Q H S a,
      (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val).Nonempty)

theorem root_kuhn_group_value_on_simplex (i : Fin 2) {T : KuhnCell 2}
    (hT : T ∈ rootKuhnMesh Q (compatibleWhitneyMeshDepth H (a+1)))
    {x : Vec 2} (hx : x ∈ T.closedCarrier) :
    (rootKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad a hfin hne i).toFun x=
      kuhnInterp T (rootGroupCorrection Q H S a hfin hne i).toFun x := by
  change zeroExtendedKuhnAffine _ _ x=_
  exact zeroExtendedKuhnAffine_of_mem_closedCarrier
    (fun U hU => root_kuhn_mesh_scale Q _ hU) _ hT hx

theorem root_kuhn_group_gradient_on_simplex (i k : Fin 2) {T : KuhnCell 2}
    (hT : T ∈ rootKuhnMesh Q (compatibleWhitneyMeshDepth H (a+1)))
    {x : Vec 2} (hx : x ∈ T.openCarrier) :
    (rootKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad a hfin hne i).grad x k=
      kuhnSlope T (rootGroupCorrection Q H S a hfin hne i).toFun k := by
  change zeroExtendedKuhnAffineCoordDeriv _ _ k x=_
  exact zeroExtendedKuhnAffineCoordDeriv_eq_of_mem_openCarrier
    (fun U hU => root_kuhn_mesh_scale Q _ hU) hT hx k

/-- Actual Kuhn values and weak derivatives occur only on the literal whole
closure-touching component neighborhood. -/
theorem stopped_kuhn_group_field_support (i : Fin 2) (n : ℕ) (P : TriadicCube 2)
    (hP : P ∈ whitneyRootLayer Q H n) (x : Vec 2) (hx : x ∈ openCubeSet P)
    (hv : (rootKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad a hfin hne i).toFun x ≠ 0 ∨
      ∃ k, (rootKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad a hfin hne i).grad x k ≠ 0) :
    ∃ C ∈ rootComponentGroup Q H S a, P ∈ rootWhitneyNeighborhood Q H C := by
  let J := compatibleWhitneyMeshDepth H (a+1)
  let b := rootGroupNodalCorrection Q H S a hfin hne i
  have hstars : x ∈ nodalClosedStars Q J b := by
    by_contra hn
    rcases hv with hv | ⟨k,hk⟩
    · exact hv (kuhn_nodal_extension_zero_off_stars Q J b hn)
    · exact hk (kuhn_nodal_derivative_zero_off_stars Q J b hn k)
  obtain ⟨z,hz,hxz⟩ := Set.mem_iUnion₂.mp hstars
  obtain ⟨C,hCz⟩ := root_group_nodal_nonzero_component Q H S a hfin hne i hz
  refine ⟨C.val,C.property,?_⟩
  apply stopped_group_node_star_neighborhood M Q H hH τ η ω hgood S hS hbad a C z hCz n P hP x hx
  intro k
  have hc : |x k-diagInteriorVertex Q J z k| ≤ ‖x-diagInteriorVertex Q J z‖ := by
    simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (x-diagInteriorVertex Q J z) k
  exact hc.trans (Metric.mem_closedBall.mp hxz)

/-- The same actual two-layer support applies simultaneously to values and
every weak-gradient coordinate of the finite-Kuhn group. -/
theorem stopped_kuhn_group_ae_support (i : Fin 2) :
    ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      ((rootKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad a hfin hne i).toFun x ≠ 0 ∨
        ∃ k, (rootKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad a hfin hne i).grad x k ≠ 0) →
          x ∈ rootLayerCarrier Q H a ∪ rootLayerCarrier Q H (a+1) := by
  filter_upwards [root_whitney_ae_interior_cover Q H] with x hx
  obtain ⟨n,P,hP,hxP⟩ := hx
  intro hv
  obtain ⟨C,hC,hPC⟩ := stopped_kuhn_group_field_support M Q H hH τ η ω hgood S hS hbad a hfin hne i n P hP x hxP hv
  have hl := stopped_group_neighborhood_layers M Q H hH τ η ω hgood S hS hbad a ⟨C,hC⟩ hPC
  rcases hl with hl | hl
  · exact Or.inl (Set.mem_iUnion₂.mpr ⟨P,hl,(openCubeSet_subset_cubeSet P) hxP⟩)
  · exact Or.inr (Set.mem_iUnion₂.mpr ⟨P,hl,(openCubeSet_subset_cubeSet P) hxP⟩)

end
end ASDExplicitGamma.Inverse
