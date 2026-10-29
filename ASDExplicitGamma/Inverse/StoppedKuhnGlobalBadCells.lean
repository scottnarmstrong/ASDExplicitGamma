module

public import ASDExplicitGamma.Inverse.StoppedKuhnBadCells
public import ASDExplicitGamma.Inverse.StoppedKuhnOtherBadGroups
public import ASDExplicitGamma.Inverse.StoppedGlobalKuhnSeries
public import ASDExplicitGamma.Inverse.StoppedGlobalKuhnMidpointMap

/-! The whole-root common Kuhn map is constant on every bad cell, with the
literal component bounding-box midpoint as its value and zero weak gradient. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Affine Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- The actual bad cell's canonical component, without a duplicate root choice. -/
def rootOwnComponent (Q : TriadicCube 2) (H : ℕ) (S : Set (TriadicCube 2))
    (V : TriadicCube 2) (hVS : V ∈ S) :
    rootComponentGroup Q H S (rootComponentLeastLayer Q H (badComponent S V)) :=
  ⟨badComponent S V,⟨⟨V,hVS,rfl⟩,rfl⟩⟩

variable (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
  (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
  (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
    (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
  (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
  (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)

/-- The source component's single bounding-box midpoint, shared by all loads. -/
def stoppedCanonicalMidpoint (V : TriadicCube 2) (hVS : V ∈ S) : Vec 2 :=
  let a := rootComponentLeastLayer Q H (badComponent S V)
  let C := rootOwnComponent Q H S V hVS
  componentMidpoint Q (compatibleWhitneyMeshDepth H (a+1))
    (componentMeshNodes Q _ C.val)
    (stopped_component_group_nodes_nonempty M Q H hH τ η ω hgood S hS hbad a C.property)

/-- The common map is exactly the source midpoint on every bad-cell interior
almost everywhere; all weak-gradient coordinates vanish there. -/
theorem stopped_global_kuhn_midpoint_ae_bad_cells (i : Fin 2) :
    ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), ∀ (V : TriadicCube 2) (hVS : V ∈ S),
      x ∈ openCubeSet V →
      (stoppedKuhnMidpointCoordinate M Q H hH τ η ω hgood S hS hbad i).toFun x=
        stoppedCanonicalMidpoint M Q H hH τ η ω hgood S hS hbad V hVS i ∧
      ∀ k, (stoppedKuhnMidpointCoordinate M Q H hH τ η ω hgood S hS hbad i).grad x k=0 := by
  have hcovers : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), ∀ a : ℕ,
      ∃ U ∈ rootKuhnMesh Q (compatibleWhitneyMeshDepth H (a+1)), x ∈ U.openCarrier :=
    ae_all_iff.mpr (fun a => root_kuhn_ae_open_cover Q _)
  filter_upwards [stopped_global_kuhn_correction_ae_hasSum M Q H hH τ η ω hgood S hS hbad i,hcovers] with x hx hcover
  intro V hVS hxV
  let a := rootComponentLeastLayer Q H (badComponent S V)
  let C := rootOwnComponent Q H S V hVS
  let hfin := stopped_component_group_finite M Q H hH τ η ω hgood S hS hbad a
  let hne := fun D : rootComponentGroup Q H S a =>
    stopped_component_group_nodes_nonempty M Q H hH τ η ω hgood S hS hbad a D.property
  obtain ⟨n,hV⟩ := (root_partition_iff_layer Q H V).mp (hS hVS)
  obtain ⟨U,hU,hxU⟩ := hcover a
  have hown := stopped_kuhn_group_flatten_bad_cell M Q H hH τ η ω hgood S hS hbad a hfin hne i C n V
    (self_mem_badComponent hVS) hV U hU x hxV hxU
  change (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).toFun x=
    stoppedCanonicalMidpoint M Q H hH τ η ω hgood S hS hbad V hVS i-x i ∧
    ∀ k, (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).grad x k= -(basisVec i k) at hown
  have hz (b : ℕ) (hb : b ≠ a) := stopped_kuhn_other_group_zero_on_bad_cell M Q H hH τ η ω hgood S hS hbad b
    (stopped_component_group_finite M Q H hH τ η ω hgood S hS hbad b)
    (fun D => stopped_component_group_nodes_nonempty M Q H hH τ η ω hgood S hS hbad b D.property) i n V hVS hV hb x hxV
  have hsumv : HasSum (fun b => (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i b).toFun x)
      ((stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).toFun x) := by
    have hh := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
      (f := fun b => (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i b).toFun x) (s := ({a} : Finset ℕ))
      (fun b hb => (hz b (by simpa only [Finset.mem_singleton] using hb)).1)
    simpa only [Finset.sum_singleton] using hh
  have hvg := hx.1.unique hsumv
  constructor
  · change (diagAffineLinear Q (basisVec i)).toFun x+
      (stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i).toFun x=_
    rw [hvg,hown.1]
    have he : (diagAffineLinear Q (basisVec i)).toFun x=x i := vecDot_basisVec_left i x
    rw [he]
    change x i+(stoppedCanonicalMidpoint M Q H hH τ η ω hgood S hS hbad V hVS i-x i)=_
    ring
  · intro k
    have hsumg : HasSum (fun b => (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i b).grad x k)
        ((stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).grad x k) := by
      have hh := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
        (f := fun b => (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i b).grad x k) (s := ({a} : Finset ℕ))
        (fun b hb => (hz b (by simpa only [Finset.mem_singleton] using hb)).2 k)
      simpa only [Finset.sum_singleton] using hh
    have hgg := (hx.2 k).unique hsumg
    change (diagAffineLinear Q (basisVec i)).grad x k+
      (stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i).grad x k=0
    rw [hgg,hown.2 k]
    change basisVec i k+ -(basisVec i k)=0
    exact add_neg_cancel _

end
end ASDExplicitGamma.Inverse
