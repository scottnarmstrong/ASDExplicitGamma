module

public import ASDExplicitGamma.Inverse.StoppedLocalizedDiameter

/-! Deterministic localization bounds for the actual in-box diameter. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open scoped ENNReal

/-- Two actual sites of a radius-N inspection box differ by at most 2N. -/
theorem block_distance_le_of_inspection_box (x y z : BlockSite) (N : ℕ)
    (hy : y ∈ blockCube (fun d => x d-(N:ℤ)) (2*N+1))
    (hz : z ∈ blockCube (fun d => x d-(N:ℤ)) (2*N+1)) :
    blockDistance y z ≤ 2*N := by
  have hd (d : Fin 2) : (z d-y d).natAbs ≤ 2*N := by
    have hy' := hy d
    have hz' := hz d
    change x d-(N:ℤ) ≤ y d ∧ y d < x d-(N:ℤ)+((2*N+1:ℕ):ℤ) at hy'
    change x d-(N:ℤ) ≤ z d ∧ z d < x d-(N:ℤ)+((2*N+1:ℕ):ℤ) at hz'
    omega
  exact max_le (hd 0) (hd 1)

/-- The true in-box diameters obey the source deterministic bound 2N+1. -/
theorem localized_diameter_field_le_box {Ω : Type*} (B : PlanarMarks Ω)
    (M N : ℕ) (x : BlockSite) (ω : Ω) :
    localizedDiameterField B M N x ω ≤ ((2*N+1:ℕ):ℝ≥0∞) := by
  classical
  let C := siteEventMarks (localizedOccupied B M N x)
  change (diameterRoots x).sup (fun u => clusterDiameter C ω u) ≤ _
  apply Finset.sup_le
  intro u _
  apply iSup_le
  intro y
  apply iSup_le
  intro z
  by_cases hp : y ∈ clusterSites C ω u ∧ z ∈ clusterSites C ω u
  · have hy := localized_cluster_subset_box B M N x u ω hp.1
    have hz := localized_cluster_subset_box B M N x u ω hp.2
    have hd := block_distance_le_of_inspection_box x y z N hy hz
    simp only [Set.indicator,Set.mem_ofPred_eq,hp.1,hp.2,true_and,ite_true]
    exact_mod_cast Nat.add_le_add_right hd 1
  · simp only [Set.indicator,Set.mem_ofPred_eq,hp,ite_false,zero_le]

end ASDExplicitGamma.Inverse
