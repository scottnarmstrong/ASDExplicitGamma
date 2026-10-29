module

public import ASDExplicitGamma.Inverse.StoppedPhysicalBlocks
public import ASDExplicitGamma.Inverse.WeightedLocalizationBlockGeometry
public import ASDExplicitGamma.Inverse.WeightedLocalizationCentering

/-! The half-open physical partition of the actual globally indexed q3 buffered blocks. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
noncomputable section

/-- Actual globally indexed half-open buffered block. Its closed carrier is
exactly the carrier already used in the completed cutoff-local proofs. -/
def physicalBlockSet (j : ℤ) (z : BlockSite) : Set (Vec 2) :=
  Set.pi Set.univ (fun d => Set.Ico
    (physicalBlockSide j*(z d:ℝ)-(3:ℝ)^j/2)
    (physicalBlockSide j*((z d:ℝ)+1)-(3:ℝ)^j/2))

theorem physical_block_set_measurable (j : ℤ) (z : BlockSite) :
    MeasurableSet (physicalBlockSet j z) := MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

/-- Exact physical area, independent of the block's lattice translate. -/
theorem physical_block_set_volume (j : ℤ) (z : BlockSite) :
    volume (physicalBlockSet j z) = ENNReal.ofReal ((physicalBlockSide j)^2) := by
  rw [physicalBlockSet,Real.volume_pi_Ico]
  have he (d : Fin 2) : (physicalBlockSide j*((z d:ℝ)+1)-(3:ℝ)^j/2)-
      (physicalBlockSide j*(z d:ℝ)-(3:ℝ)^j/2) = physicalBlockSide j := by ring
  simp_rw [he]
  rw [Fin.prod_univ_two,← ENNReal.ofReal_mul (physical_block_side_pos j).le]
  congr 1
  ring

/-- The actual physical block containing a point, including all half-open
boundary points and all negative lattice coordinates. -/
def physicalBlockIndex (j : ℤ) (p : Vec 2) : BlockSite :=
  fun d => ⌊(p d+(3:ℝ)^j/2)/physicalBlockSide j⌋

theorem physical_block_index_mem (j : ℤ) (p : Vec 2) :
    p ∈ physicalBlockSet j (physicalBlockIndex j p) := by
  intro d _
  have hW := physical_block_side_pos j
  have hl := (le_div_iff₀ hW).mp (Int.floor_le ((p d+(3:ℝ)^j/2)/physicalBlockSide j))
  have hu := (div_lt_iff₀ hW).mp (Int.lt_floor_add_one ((p d+(3:ℝ)^j/2)/physicalBlockSide j))
  change physicalBlockSide j*(physicalBlockIndex j p d:ℝ)-(3:ℝ)^j/2 ≤ p d ∧
    p d < physicalBlockSide j*((physicalBlockIndex j p d:ℝ)+1)-(3:ℝ)^j/2
  change (physicalBlockIndex j p d:ℝ)*physicalBlockSide j ≤ p d+(3:ℝ)^j/2 at hl
  change p d+(3:ℝ)^j/2 < ((physicalBlockIndex j p d:ℝ)+1)*physicalBlockSide j at hu
  constructor <;> nlinarith only [hl,hu]

theorem physical_block_index_eq_iff (j : ℤ) (p : Vec 2) (z : BlockSite) :
    physicalBlockIndex j p = z ↔ p ∈ physicalBlockSet j z := by
  constructor
  · intro he
    rw [← he]
    exact physical_block_index_mem j p
  · intro hp
    funext d
    apply Int.floor_eq_iff.mpr
    have hd := hp d (Set.mem_univ d)
    have hW := physical_block_side_pos j
    constructor
    · apply (le_div_iff₀ hW).mpr
      nlinarith only [hd.1]
    · apply (div_lt_iff₀ hW).mpr
      nlinarith only [hd.2]

/-- Distinct actual q3 block indices give disjoint half-open carriers. -/
theorem physical_block_sets_disjoint (j : ℤ) :
    Pairwise (fun z z' => Disjoint (physicalBlockSet j z) (physicalBlockSet j z')) := by
  intro z z' hne
  apply Set.disjoint_left.mpr
  intro p hp hp'
  exact hne (((physical_block_index_eq_iff j p z).mpr hp).symm.trans
    ((physical_block_index_eq_iff j p z').mpr hp'))

end
end ASDExplicitGamma.Inverse
