module

public import ASDExplicitGamma.Inverse.StoppedPathProbability

/-! The actual occupied component radius is controlled by the proved finite path event. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open SimpleGraph MeasureTheory
noncomputable section

/-- Graph walk length bounds every actual block-coordinate displacement. -/
theorem occupied_walk_coordinate_distance {O : Set BlockSite} {x y : O}
    (p : (blockGraph.induce O).Walk x y) (d : Fin 2) :
    |y.val d-x.val d| ≤ (p.length:ℤ) := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
    have hstep : |y.val d-x.val d| ≤ 1 := h.2 d
    calc
      _ = |(z.val d-y.val d)+(y.val d-x.val d)| := by congr 1; omega
      _ ≤ |z.val d-y.val d|+|y.val d-x.val d| := abs_add_le _ _
      _ ≤ (p.length:ℤ)+1 := add_le_add ih hstep
      _ = _ := by simp only [Walk.length_cons,Nat.cast_add,Nat.cast_one]

/-- A component reaches integer block radius R when it contains an actually
connected occupied endpoint at that coordinate displacement. -/
def clusterReaches {Ω : Type*} (B : PlanarMarks Ω) (x : BlockSite) (R : ℕ) : Set Ω :=
  {ω | ∃ hx : x ∈ markedOccupied B ω, ∃ y : markedOccupied B ω,
    (blockGraph.induce (markedOccupied B ω)).Reachable ⟨x,hx⟩ y ∧
      ∃ d, (R:ℤ) ≤ |y.val d-x d|}

/-- A component reaching radius R contains an actual shortest occupied prefix
of exactly R edges, so no infinite family of endpoint choices is counted. -/
theorem cluster_reaches_subset_shortest {Ω : Type*} (B : PlanarMarks Ω)
    (x : BlockSite) (R : ℕ) : clusterReaches B x R ⊆ shortestOccupiedLengthEvent B x R := by
  intro ω hω
  obtain ⟨hx,y,hr,d,hd⟩ := hω
  obtain ⟨p,hp⟩ := hr.exists_walk_length_eq_dist
  have hR : R ≤ p.length := by
    have hh := occupied_walk_coordinate_distance p d
    have hRZ : (R:ℤ) ≤ (p.length:ℤ) := hd.trans hh
    exact_mod_cast hRZ
  let q := p.take R
  have hq : q.length = R := by
    rw [Walk.take_length]
    exact Nat.min_eq_left hR
  have hdist := length_eq_dist_of_subwalk hp (p.isSubwalk_take R)
  exact ⟨hx,p.getVert R,q,hq,hdist⟩

/-- The actual occupied cluster has the source exponential radius tail.
The stronger coefficient one follows from the conservative finite route budget. -/
theorem cluster_radius_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (x : BlockSite) (R : ℕ) :
    μ.real (clusterReaches B x R) ≤ Real.exp (-(R:ℝ)/2) :=
  (measureReal_mono (cluster_reaches_subset_shortest B x R)).trans
    (shortest_occupied_path_probability μ B q hB hq0 hq x R)

end
end ASDExplicitGamma.Inverse
