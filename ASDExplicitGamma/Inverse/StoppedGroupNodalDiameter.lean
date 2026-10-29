module

public import ASDExplicitGamma.Inverse.StoppedMeshHatBounds
public import ASDExplicitGamma.Triadic.DiagInterpolant
public import ASDExplicitGamma.Triadic.PlanarDirectionLinear
public import ASDExplicitGamma.Inverse.StoppedGroupSupport
public import ASDExplicitGamma.Inverse.StoppedGroupFallback
public import ASDExplicitGamma.Inverse.StoppedNeighborComponentSpan
public import ASDExplicitGamma.Inverse.StoppedRootLiftUniqueness

/-! Physical local-Z bound for every actual nonzero midpoint node whose
closed source star contains the current cell point. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
open scoped ENNReal
noncomputable section

theorem stopped_group_node_diameter_bound (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (a : ℕ) (hfin : (rootComponentGroup Q H S a).Finite)
    (hne : ∀ C : rootComponentGroup Q H S a,
      (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val).Nonempty)
    (i : Fin 2) (n : ℕ) (P T : TriadicCube 2)
    (hP : P ∈ whitneyRootLayer Q H n)
    (hPT : RootWhitneyLift Q (a+whitneyProfile H a) P T)
    (hfinite : diameterField (q3PlanarMarks M (Q.scale-(a+whitneyProfile H a)) τ η)
      ω (fineBlockIndex T.index) ≠ ∞)
    (x : Vec 2) (hx : x ∈ openCubeSet P)
    (z : InteriorNode (compatibleWhitneyMeshDepth H (a+1)))
    (hz : rootGroupNodalCorrection Q H S a hfin hne i z ≠ 0)
    (hnear : ∀ k, |x k-diagInteriorVertex Q (compatibleWhitneyMeshDepth H (a+1)) z k| ≤
      diagMeshRadius Q (compatibleWhitneyMeshDepth H (a+1))) :
    |rootGroupNodalCorrection Q H S a hfin hne i z| ≤
      (3:ℝ)^40*realDiameterField
        (q3PlanarMarks M (Q.scale-(a+whitneyProfile H a)) τ η) (fineBlockIndex T.index) ω*
        (3:ℝ)^(Q.scale-((a+whitneyProfile H a:ℕ):ℤ)) := by
  let J := compatibleWhitneyMeshDepth H (a+1)
  obtain ⟨C,hCz⟩ := root_group_nodal_nonzero_component Q H S a hfin hne i hz
  have hPC := stopped_group_node_star_neighborhood M Q H hH τ η ω hgood S hS hbad a C z hCz n P hP x hx hnear
  obtain ⟨R,hR,he⟩ := C.property.1
  have ha : rootComponentLeastLayer Q H (badComponent S R)=a := by rw [← he]; exact C.property.2
  have hh := stopped_neighbor_component_span M Q H hH τ η ω hgood S hS hbad R hR P (by rwa [← he])
  dsimp only at hh
  rw [ha] at hh
  obtain ⟨T',hPT',hspan⟩ := hh
  have heT := root_whitney_lift_unique hPT' hPT
  subst T'
  simp only [← he] at hspan
  have hbd := (hspan hfinite).2 J (hne C) i
  rw [root_group_nodal_on_component Q H S a hfin hne C hCz i]
  apply (component_midpoint_displacement_bound Q J _ (hne C) z hCz i).trans
  have hh' := div_le_div_of_nonneg_right hbd (by norm_num : (0:ℝ) ≤ 2)
  simp only [Nat.cast_add,sub_add_eq_sub_sub] at hh' ⊢
  convert hh' using 1
  ring

end
end ASDExplicitGamma.Inverse
