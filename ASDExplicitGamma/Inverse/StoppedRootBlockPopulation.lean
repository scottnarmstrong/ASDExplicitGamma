module

public import ASDExplicitGamma.Inverse.StoppedPhysicalBlockPartition

/-! Deterministic finite physical block populations covering the actual source root. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
noncomputable section

/-- The fine label whose buffered side is the source resolution of the root. -/
def rootFineLabel (Q : TriadicCube 2) (R : ℕ) : ℤ := Q.scale-R-40

/-- Lower and upper physical vertices of the half-open root. -/
def rootVertex (Q : TriadicCube 2) (upper : Bool) : Vec 2 :=
  fun d => ((Q.index d:ℝ)+(if upper then 1/2 else -(1/2)))*cubeScaleFactor Q

/-- All actual global block indices between the two root vertices. Extra
zero-weight blocks are retained; the population uses no random selection. -/
def rootBlockPopulation (Q : TriadicCube 2) (R : ℕ) : Finset BlockSite :=
  Fintype.piFinset (fun d => Finset.Icc
    (physicalBlockIndex (rootFineLabel Q R) (rootVertex Q false) d)
    (physicalBlockIndex (rootFineLabel Q R) (rootVertex Q true) d))

/-- The physical block index is monotone in each spatial coordinate. -/
theorem physical_block_index_mono (j : ℤ) (p q : Vec 2) (hpq : p ≤ q) :
    physicalBlockIndex j p ≤ physicalBlockIndex j q := by
  intro d
  apply Int.floor_mono
  exact div_le_div_of_nonneg_right (add_le_add (hpq d) le_rfl) (physical_block_side_pos j).le

/-- Every point of the actual root has its global block in this finite population. -/
theorem root_block_population_mem (Q : TriadicCube 2) (R : ℕ) (p : Vec 2)
    (hp : p ∈ cubeSet Q) :
    physicalBlockIndex (rootFineLabel Q R) p ∈ rootBlockPopulation Q R := by
  have hl : rootVertex Q false ≤ p := by
    intro d
    have hd := (hp d).1
    change ((Q.index d:ℝ)-1/2)*cubeScaleFactor Q ≤ p d at hd
    simpa only [rootVertex, Bool.false_eq_true, ite_false, sub_eq_add_neg] using hd
  have hu : p ≤ rootVertex Q true := by
    intro d
    have hd := (hp d).2.le
    change p d ≤ ((Q.index d:ℝ)+1/2)*cubeScaleFactor Q at hd
    simpa only [rootVertex, ite_true] using hd
  rw [rootBlockPopulation,Fintype.mem_piFinset]
  intro d
  exact Finset.mem_Icc.mpr ⟨physical_block_index_mono _ _ _ hl d,
    physical_block_index_mono _ _ _ hu d⟩

/-- The finite deterministic population covers the entire source root. -/
theorem root_block_population_cover (Q : TriadicCube 2) (R : ℕ) :
    cubeSet Q ⊆ ⋃ z : ↥(rootBlockPopulation Q R),
      physicalBlockSet (rootFineLabel Q R) z.val := by
  intro p hp
  exact Set.mem_iUnion.mpr ⟨⟨physicalBlockIndex (rootFineLabel Q R) p,
    root_block_population_mem Q R p hp⟩,physical_block_index_mem _ _⟩

end
end ASDExplicitGamma.Inverse
