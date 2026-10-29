module

public import ASDExplicitGamma.Inverse.StoppedCubeCharge
public import ASDExplicitGamma.Inverse.StoppedRouteCharge
public import ASDExplicitGamma.Inverse.StoppedIndependentMarks

/-! Literal local-plus-activation charge of every actual shortest occupied path. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open SimpleGraph
open scoped BigOperators
noncomputable section

/-- Each site's positive activation is read at its unique aligned cube. -/
theorem occupied_through_iff {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω)
    (N : ℕ) (x : BlockSite) :
    x ∈ markedOccupiedThrough B N ω ↔ ω ∈ B.localMark x ∨
      ∃ n < N, ω ∈ positiveActivation B n (alignedCubeIndex (3^(n+1)) x) := by
  constructor
  · rintro (hlocal | ⟨n,hn,i,hi,hx⟩)
    · exact Or.inl hlocal
    · have he := (aligned_cube_index_iff (3^(n+1)) (by positivity) x i).mpr hx
      exact Or.inr ⟨n,hn,by simpa only [he] using hi⟩
  · rintro (hlocal | ⟨n,hn,hi⟩)
    · exact Or.inl hlocal
    · exact Or.inr ⟨n,hn,_,hi,mem_own_aligned_cube _ (by positivity) x⟩

/-- Every occupied site contributes at least one literal mark at a sufficiently
large finite label cutoff. Overlapping activations are counted positively. -/
theorem occupied_site_charge {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω)
    (N : ℕ) (x : BlockSite) (hx : x ∈ markedOccupiedThrough B N ω) :
    (1:ℝ) ≤ markIndicator (B.localMark x) ω+
      ∑ n ∈ Finset.range N, markIndicator
        (positiveActivation B n (alignedCubeIndex (3^(n+1)) x)) ω := by
  classical
  have hn : 0 ≤ ∑ n ∈ Finset.range N, markIndicator
      (positiveActivation B n (alignedCubeIndex (3^(n+1)) x)) ω :=
    Finset.sum_nonneg (fun n _ => (mark_indicator_bounds _ _).1)
  rcases (occupied_through_iff B ω N x).mp hx with hlocal | ⟨n,hlt,hi⟩
  · simp only [markIndicator,Set.indicator_of_mem hlocal] at *
    linarith only [hn]
  · have hh := Finset.single_le_sum (fun n _ => (mark_indicator_bounds
      (positiveActivation B n (alignedCubeIndex (3^(n+1)) x)) ω).1) (Finset.mem_range.mpr hlt)
    have hi' : markIndicator (positiveActivation B n (alignedCubeIndex (3^(n+1)) x)) ω = 1 :=
      by simp only [markIndicator,Set.indicator_of_mem hi]
    rw [hi'] at hh
    exact hh.trans (le_add_of_nonneg_left (mark_indicator_bounds (B.localMark x) ω).1)

/-- Every finite collection of full occupied sites has one common finite label
cutoff. The observed cutoff is allowed to depend on the sample. -/
theorem finite_occupied_label_cutoff {Ω I : Type*} [Fintype I]
    (B : PlanarMarks Ω) (ω : Ω) (x : I → markedOccupied B ω) :
    ∃ N, ∀ i, (x i).val ∈ markedOccupiedThrough B N ω := by
  classical
  have hx (i : I) : ∃ N, (x i).val ∈ markedOccupiedThrough B N ω := by
    have hh := (marked_occupied_eq_union B ω).le (x i).property
    exact Set.mem_iUnion.mp hh
  choose f hf using hx
  refine ⟨Finset.univ.sup f,fun i => ?_⟩
  exact marked_occupied_through_mono B ω
    (Finset.le_sup (f := f) (Finset.mem_univ i)) (hf i)

/-- The actual shortest occupied path pays the source local-plus-side-weighted
activation charge on one finite label population; it assumes no cluster tail. -/
theorem shortest_occupied_path_charge {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω)
    {u v : markedOccupied B ω} (p : (blockGraph.induce (markedOccupied B ω)).Walk u v)
    (hp : p.length = (blockGraph.induce (markedOccupied B ω)).dist u v) :
    ∃ N, ((p.length+1:ℕ):ℝ) ≤
      (∑ k : Fin (p.length+1), markIndicator (B.localMark (p.getVert k.val).val) ω)+
      ∑ n ∈ Finset.range N,
        ∑ i ∈ Finset.univ.image (fun k : Fin (p.length+1) => alignedCubeIndex (3^(n+1)) (p.getVert k.val).val),
          ((3^(n+1):ℕ):ℝ)*markIndicator (positiveActivation B n i) ω := by
  obtain ⟨N,hN⟩ := finite_occupied_label_cutoff B ω (fun k : Fin (p.length+1) => p.getVert k.val)
  refine ⟨N,?_⟩
  have hh := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin (p.length+1)))) =>
    occupied_site_charge B ω N (p.getVert k.val).val (hN k))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
    Finset.sum_add_distrib] at hh
  rw [Finset.sum_comm] at hh
  exact hh.trans (add_le_add le_rfl (Finset.sum_le_sum (fun n _ => positive_path_cube_charge B ω p hp n)))

/-- The shortest-path charge is exactly the fixed-route functional used by
the finite probability estimates, including every physical side weight. -/
theorem shortest_occupied_route_charge {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω)
    {u v : markedOccupied B ω} (p : (blockGraph.induce (markedOccupied B ω)).Walk u v)
    (hp : p.length = (blockGraph.induce (markedOccupied B ω)).dist u v) :
    ∃ N, ((p.length+1:ℕ):ℝ) ≤ routeCharge B (fun k : Fin (p.length+1) => (p.getVert k.val).val) N ω := by
  obtain ⟨N,hN⟩ := shortest_occupied_path_charge B ω p hp
  refine ⟨N,?_⟩
  simpa only [routeCharge,positiveLabelSide,Nat.cast_pow,Nat.cast_ofNat,Finset.mul_sum] using! hN

end
end ASDExplicitGamma.Inverse
