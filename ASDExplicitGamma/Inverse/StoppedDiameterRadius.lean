module

public import ASDExplicitGamma.Inverse.StoppedClusterDiameter

/-! Actual component diameters are controlled by occupied component radii. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open scoped ENNReal
noncomputable section

/-- A component failing to reach radius R has every member within that radius. -/
theorem cluster_member_distance_of_not_reaches {Ω : Type*}
    (B : PlanarMarks Ω) (ω : Ω) (x : BlockSite) (R : ℕ)
    (hR : ω ∉ clusterReaches B x R) {y : BlockSite}
    (hy : y ∈ clusterSites B ω x) (d : Fin 2) : |y d-x d| < (R:ℤ) := by
  by_contra! hd
  obtain ⟨hx,hy,hr⟩ := hy
  exact hR ⟨hx,⟨y,hy⟩,hr,d,hd⟩

/-- The literal component diameter plus one is bounded using its actual root
radius; no artificial box diameter is substituted for the random field. -/
theorem cluster_diameter_le_of_not_reaches {Ω : Type*}
    (B : PlanarMarks Ω) (ω : Ω) (x : BlockSite) (R : ℕ)
    (hR : ω ∉ clusterReaches B x R) :
    clusterDiameter B ω x ≤ ((2*R+1:ℕ):ℝ≥0∞) := by
  classical
  apply iSup_le
  intro y
  apply iSup_le
  intro z
  by_cases hp : y ∈ clusterSites B ω x ∧ z ∈ clusterSites B ω x
  · have hdist (d : Fin 2) : (z d-y d).natAbs ≤ 2*R := by
      have hy := abs_lt.mp (cluster_member_distance_of_not_reaches B ω x R hR hp.1 d)
      have hz := abs_lt.mp (cluster_member_distance_of_not_reaches B ω x R hR hp.2 d)
      omega
    have hn : blockDistance y z+1 ≤ 2*R+1 :=
      Nat.add_le_add_right (max_le (hdist 0) (hdist 1)) 1
    simp only [Set.indicator,Set.mem_ofPred_eq,hp.1,hp.2,true_and,ite_true]
    exact_mod_cast hn
  · simp only [Set.indicator,Set.mem_ofPred_eq,hp,ite_false,zero_le]

/-- A large radius-two diameter field forces a large genuine component
radius at one of its exactly 25 neighboring roots. -/
theorem diameter_exceed_subset_radius {Ω : Type*} (B : PlanarMarks Ω)
    (x : BlockSite) (R : ℕ) :
    {ω | ((2*R+1:ℕ):ℝ≥0∞) < diameterField B ω x} ⊆
      ⋃ y ∈ diameterRoots x, clusterReaches B y R := by
  intro ω hω
  by_contra! hn
  have hnr : ∀ y ∈ diameterRoots x, ω ∉ clusterReaches B y R := by
    intro y hy hreach
    exact hn (Set.mem_iUnion₂.mpr ⟨y,hy,hreach⟩)
  have hb : diameterField B ω x ≤ ((2*R+1:ℕ):ℝ≥0∞) :=
    Finset.sup_le (fun y hy => cluster_diameter_le_of_not_reaches B ω y R (hnr y hy))
  exact not_lt_of_ge hb hω

end
end ASDExplicitGamma.Inverse
