module

public import ASDExplicitGamma.Inverse.StoppedRealDiameter
public import ASDExplicitGamma.Inverse.StoppedElementaryCoverage
public import ASDExplicitGamma.Inverse.StoppedPhysicalContainment
public import Algsuperdiff.Section3.Provider.Whitney.PartitionCovering

/-! Actual closed-cell coordinate spans are charged to the literal cluster
diameter field, including the fine half-cell endpoints and radius-two roots. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3.Provider
open scoped ENNReal
noncomputable section

/-- Every pair of actual component members pays its distance plus one into
the literal extended diameter. -/
theorem cluster_member_pair_diameter {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω)
    (r : BlockSite) {u v : BlockSite}
    (hu : u ∈ clusterSites B ω r) (hv : v ∈ clusterSites B ω r) :
    ((blockDistance u v+1:ℕ):ℝ≥0∞) ≤ clusterDiameter B ω r := by
  unfold clusterDiameter
  apply le_iSup_of_le u
  apply le_iSup_of_le v
  simp only [Set.indicator,Set.mem_ofPred_eq,hu,hv,true_and,ite_true,le_refl]

/-- The radius-two neighborhood contains precisely every root with both
coordinate displacements at most two. -/
theorem diameter_root_of_near (x r : BlockSite) (hr : ∀ d, |r d-x d| ≤ 2) :
    r ∈ diameterRoots x := by
  apply (mem_cube_sites _ _ _).mpr
  intro d
  have hd := abs_le.mp (hr d)
  change x d-2 ≤ r d ∧ r d < x d-2+(5:ℤ)
  omega

/-- The ordinary source Z controls every pair of members of any component
whose occupied root lies in its actual radius-two neighborhood. -/
theorem real_diameter_member_pair {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω)
    (x r : BlockSite) (hr : ∀ d, |r d-x d| ≤ 2)
    (hfinite : diameterField B ω x ≠ ∞) {u v : BlockSite}
    (hu : u ∈ clusterSites B ω r) (hv : v ∈ clusterSites B ω r) :
    ((blockDistance u v+1:ℕ):ℝ) ≤ realDiameterField B x ω := by
  have hroot := diameter_root_of_near x r hr
  have hh := (cluster_member_pair_diameter B ω r hu hv).trans
    (Finset.le_sup (f := fun y => clusterDiameter B ω y) hroot)
  have ht := ENNReal.toReal_mono hfinite hh
  simpa only [realDiameterField,ENNReal.toReal_natCast] using! ht

/-- The actual closed parent cube is contained in its actual physical block;
negative fine indices use the same Euclidean division as the source field. -/
theorem fine_parent_closed_in_block (j : ℤ) (x : BlockSite) :
    Metric.closedBall (cubeCenter (⟨j,x⟩ : TriadicCube 2)) (cubeRadius (⟨j,x⟩ : TriadicCube 2)) ⊆
      physicalBlockRegion j (fineBlockIndex x) 1 := by
  obtain ⟨i,hi⟩ := buffered_parent_covers j x
  rw [← Whitney.closure_cubeSet_eq_closedBall]
  apply closure_minimal _ (physical_block_region_closed j _ 1)
  rw [← hi]
  exact buffered_parent_contained j (fineBlockIndex x) i

/-- Two points in actual physical blocks cost exactly one full block beyond
their index displacement; no additional collar or cell width is added. -/
theorem physical_block_point_span (j : ℤ) (u v : BlockSite) {p q : Vec 2}
    (hp : p ∈ physicalBlockRegion j u 1) (hq : q ∈ physicalBlockRegion j v 1)
    (d : Fin 2) :
    |p d-q d| ≤ physicalBlockSide j*((blockDistance u v+1:ℕ):ℝ) := by
  have hp' := hp d
  have hq' := hq d
  have hd : (|(v d-u d)|:ℝ) ≤ (blockDistance u v:ℝ) := by
    have hn : (v d-u d).natAbs ≤ blockDistance u v := by
      fin_cases d
      · exact le_max_left _ _
      · exact le_max_right _ _
    have hint : ((v d-u d).natAbs:ℤ) ≤ (blockDistance u v:ℤ) := by exact_mod_cast hn
    rw [← Int.abs_eq_natAbs] at hint
    exact_mod_cast hint
  have hdist := abs_le.mp hd
  have hside := physical_block_side_pos j
  have hm0 := mul_le_mul_of_nonneg_left hdist.1 hside.le
  have hm1 := mul_le_mul_of_nonneg_left hdist.2 hside.le
  rw [abs_le]
  norm_num only [Nat.cast_one,Nat.cast_add,Int.cast_sub] at hp' hq' hm0 hm1 ⊢
  constructor <;> nlinarith only [hp'.1,hp'.2,hq'.1,hq'.2,hm0,hm1]

/-- Literal Z controls the whole physical closed-cell span once their parent
blocks belong to one of its actual neighboring components. -/
theorem physical_cluster_point_span {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω)
    (j : ℤ) (x r u v : BlockSite) (hr : ∀ d, |r d-x d| ≤ 2)
    (hfinite : diameterField B ω x ≠ ∞)
    (hu : u ∈ clusterSites B ω r) (hv : v ∈ clusterSites B ω r)
    {p q : Vec 2} (hp : p ∈ physicalBlockRegion j u 1)
    (hq : q ∈ physicalBlockRegion j v 1) (d : Fin 2) :
    |p d-q d| ≤ 2*(3:ℝ)^40*realDiameterField B x ω*(3:ℝ)^j := by
  apply (physical_block_point_span j u v hp hq d).trans
  have hz := real_diameter_member_pair B ω x r hr hfinite hu hv
  have hh := mul_le_mul_of_nonneg_left hz (physical_block_side_pos j).le
  rw [physical_block_side_eq] at hh
  simpa only [physical_block_side_eq,mul_assoc,mul_left_comm,mul_comm] using! hh

end
end ASDExplicitGamma.Inverse
