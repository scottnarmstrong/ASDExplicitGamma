module

public import ASDExplicitGamma.Inverse.StoppedMarkedField
public import ASDExplicitGamma.Inverse.StoppedCubeVisits
public import ASDExplicitGamma.Inverse.StoppedBernoulliMGF

/-! Pathwise charging to the actual finite set of activated cubes met by a shortest path. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open SimpleGraph
open scoped BigOperators
noncomputable section

/-- A shortest path has at most side indices in any wholly occupied aligned cube. -/
theorem shortest_aligned_visit_card {O : Set BlockSite} {u v : O}
    (p : (blockGraph.induce O).Walk u v) (hp : p.length = (blockGraph.induce O).dist u v)
    (side : ℕ) (hs : 0 < side) (i : BlockSite)
    (hO : blockCube (alignedCubeBase side i) side ⊆ O) :
    (Finset.univ.filter (fun k : Fin (p.length+1) => alignedCubeIndex side (p.getVert k.val).val = i)).card ≤ side := by
  classical
  have he : (Finset.univ.filter (fun k : Fin (p.length+1) => alignedCubeIndex side (p.getVert k.val).val = i)) =
      pathCubeVisits p (alignedCubeBase side i) side := by
    ext k
    simp only [pathCubeVisits,Finset.mem_filter,Finset.mem_univ,true_and,
      aligned_cube_index_iff side hs]
  rw [he]
  exact shortest_cube_visit_card p hp (alignedCubeBase side i) side hO

/-- The cube charge uses distinct aligned cubes, each with its literal side
weight; repeated visits are accounted for by shortest-path geometry. -/
theorem positive_path_cube_charge {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω)
    {u v : markedOccupied B ω} (p : (blockGraph.induce (markedOccupied B ω)).Walk u v)
    (hp : p.length = (blockGraph.induce (markedOccupied B ω)).dist u v) (n : ℕ) :
    (∑ k : Fin (p.length+1), markIndicator
      (positiveActivation B n (alignedCubeIndex (3^(n+1)) (p.getVert k.val).val)) ω) ≤
    ∑ i ∈ Finset.univ.image (fun k : Fin (p.length+1) => alignedCubeIndex (3^(n+1)) (p.getVert k.val).val),
      ((3^(n+1):ℕ):ℝ)*markIndicator (positiveActivation B n i) ω := by
  classical
  let f (k : Fin (p.length+1)) := alignedCubeIndex (3^(n+1)) (p.getVert k.val).val
  let A := Finset.univ.image f
  have hf : ∀ k ∈ (Finset.univ : Finset (Fin (p.length+1))), f k ∈ A :=
    fun k hk => Finset.mem_image.mpr ⟨k,hk,rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to' hf (fun i => markIndicator (positiveActivation B n i) ω)]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.sum_const,nsmul_eq_mul]
  by_cases hact : ω ∈ positiveActivation B n i
  · have hc := shortest_aligned_visit_card p hp (3^(n+1)) (by positivity) i
      (active_cube_occupied B ω n i hact)
    have hh : (((Finset.univ.filter (fun k : Fin (p.length+1) => f k = i)).card):ℝ) ≤ ((3^(n+1):ℕ):ℝ) :=
      by exact_mod_cast hc
    exact mul_le_mul_of_nonneg_right hh (by simp [markIndicator,hact])
  · simp only [markIndicator,Set.indicator_of_notMem hact,mul_zero,le_refl]

end
end ASDExplicitGamma.Inverse
