module

public import ASDExplicitGamma.Inverse.StoppedPhysicalBlockPartition
public import ASDExplicitGamma.Inverse.StoppedPhysicalContainment
public import ASDExplicitGamma.Inverse.StoppedFineBlockMap
public import ASDExplicitGamma.Inverse.StoppedRootWhitneyLift

/-! The actual pointwise physical block index equals the blocked integer
index of its genuine fine ancestor, including negative lattice coordinates. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
noncomputable section

theorem fine_cube_physical_block (T : TriadicCube 2) :
    cubeSet T ⊆ physicalBlockSet T.scale (fineBlockIndex T.index) := by
  intro x hx d _
  have hi := fine_block_index_bounds T.index d
  have hlow : 2*(3:ℝ)^40*(fineBlockIndex T.index d:ℝ) ≤ (T.index d:ℝ) := by exact_mod_cast hi.1
  have huZ : T.index d+1 ≤ (2*3^40:ℤ)*(fineBlockIndex T.index d+1) := by omega
  have hupp : (T.index d:ℝ)+1 ≤ 2*(3:ℝ)^40*((fineBlockIndex T.index d:ℝ)+1) := by exact_mod_cast huZ
  have hs : 0 ≤ (3:ℝ)^T.scale := (zpow_pos (by norm_num) _).le
  have hl := mul_le_mul_of_nonneg_right hlow hs
  have hu := mul_le_mul_of_nonneg_right hupp hs
  have hp := hx d
  change ((T.index d:ℝ)-1/2)*(3:ℝ)^T.scale ≤ x d ∧
    x d < ((T.index d:ℝ)+1/2)*(3:ℝ)^T.scale at hp
  change physicalBlockSide T.scale*(fineBlockIndex T.index d:ℝ)-(3:ℝ)^T.scale/2 ≤ x d ∧
    x d < physicalBlockSide T.scale*((fineBlockIndex T.index d:ℝ)+1)-(3:ℝ)^T.scale/2
  rw [physical_block_side_eq]
  constructor <;> linarith only [hp.1,hp.2,hl,hu]

theorem fine_cube_physical_block_index (T : TriadicCube 2) {x : Vec 2} (hx : x ∈ cubeSet T) :
    physicalBlockIndex T.scale x=fineBlockIndex T.index :=
  (physical_block_index_eq_iff _ _ _).mpr (fine_cube_physical_block T hx)

/-- A lifted current cell uses exactly its ancestor's source Z block at
every point of its half-open carrier. -/
theorem root_whitney_lift_physical_block_index {Q P T : TriadicCube 2} {base : ℕ}
    (hPT : RootWhitneyLift Q base P T) {x : Vec 2} (hx : x ∈ cubeSet P) :
    physicalBlockIndex (Q.scale-(base:ℤ)) x=fineBlockIndex T.index := by
  have hs := scale_eq_sub_of_mem_descendantsAtDepth hPT.1
  obtain ⟨r,hr,hP⟩ := hPT.2
  rw [← hs]
  exact fine_cube_physical_block_index T (cubeSet_subset_of_mem_descendantsAtDepth hP hx)

end
end ASDExplicitGamma.Inverse
