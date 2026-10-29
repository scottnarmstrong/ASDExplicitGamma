module

public import ASDExplicitGamma.Inverse.StoppedOccupiedRoute
public import ASDExplicitGamma.Inverse.StoppedPathCharge
public import ASDExplicitGamma.Inverse.StoppedRouteLimit

/-! Actual shortest occupied path events are covered by deterministic finite candidate populations. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory SimpleGraph
noncomputable section

/-- The actual event that a shortest occupied path of the specified length
starts at x. Endpoints may be anywhere in the infinite occupied graph. -/
def shortestOccupiedLengthEvent {Ω : Type*} (B : PlanarMarks Ω) (x : BlockSite) (R : ℕ) : Set Ω :=
  {ω | ∃ hx : x ∈ markedOccupied B ω, ∃ y : markedOccupied B ω,
    ∃ p : (blockGraph.induce (markedOccupied B ω)).Walk ⟨x,hx⟩ y,
      p.length = R ∧ p.length = (blockGraph.induce (markedOccupied B ω)).dist ⟨x,hx⟩ y}

/-- A fixed candidate needs the purely deterministic parity-separation
condition; its probability event is the actual finite-witness charge event. -/
def candidateRouteEvent {Ω : Type*} (B : PlanarMarks Ω) (x : BlockSite) (R : ℕ)
    (r : BlockRoutes x R) : Set Ω := by
  classical
  exact if RouteParitySeparated (blockRouteVertices x R r) then
    {ω | ∃ N, ((R+1:ℕ):ℝ) ≤ routeCharge B (blockRouteVertices x R r) N ω} else ∅

/-- Actual shortest occupied paths land in the finite candidate union. Neither
random endpoints nor sample-selected label cutoffs enlarge that population. -/
theorem shortest_event_subset_candidates {Ω : Type*} (B : PlanarMarks Ω) (x : BlockSite) (R : ℕ) :
    shortestOccupiedLengthEvent B x R ⊆ ⋃ r : BlockRoutes x R, candidateRouteEvent B x R r := by
  classical
  intro ω hω
  obtain ⟨hx,y,p,hR,hp⟩ := hω
  subst R
  let r := occupiedWalkRoute p
  refine Set.mem_iUnion.mpr ⟨r,?_⟩
  have hpar : RouteParitySeparated (blockRouteVertices x p.length r) :=
    occupied_route_parity_separated p hp
  change ω ∈ candidateRouteEvent B x p.length r
  rw [candidateRouteEvent,ite_eq_left hpar]
  obtain ⟨N,hN⟩ := shortest_occupied_route_charge B ω p hp
  refine ⟨N,?_⟩
  have he : blockRouteVertices x p.length r = (fun k : Fin (p.length+1) => (p.getVert k.val).val) := by
    funext k
    exact occupied_route_vertex p k.val
  rw [he]
  exact hN

/-- Every fixed candidate has the same infinite-label charge bound; no
independence across labels or selection cutoff is assumed. -/
theorem candidate_route_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (x : BlockSite) (R : ℕ) (r : BlockRoutes x R) :
    μ.real (candidateRouteEvent B x R r) ≤ Real.exp (-(49/10:ℝ)*((R+1:ℕ):ℝ)) := by
  classical
  unfold candidateRouteEvent
  split_ifs with hp
  · exact control_route_full_charge_tail μ B q hB hq0 hq _ hp
  · simp only [measureReal_empty]
    exact (Real.exp_pos _).le

end
end ASDExplicitGamma.Inverse
