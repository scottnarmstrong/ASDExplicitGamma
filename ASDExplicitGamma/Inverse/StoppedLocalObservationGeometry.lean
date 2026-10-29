module

public import ASDExplicitGamma.Inverse.StoppedPhysicalBlocks
public import ASDExplicitGamma.Inverse.StoppedLocalizedDiameter

/-! The complete retained raw populations fit in the source double observation box. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
noncomputable section

/-- Every raw site of the aligned cube containing y is less than one side
from y in every coordinate, even when that raw site is outside the box. -/
theorem same_aligned_cube_distance (s : ℕ) (hs : 0 < s) (y z : BlockSite)
    (hz : z ∈ blockCube (alignedCubeBase s (alignedCubeIndex s y)) s) (d : Fin 2) :
    |z d-y d| < (s:ℤ) := by
  have hy := mem_own_aligned_cube s hs y d
  have hz' := hz d
  rw [abs_lt]
  constructor <;> omega

/-- All outside raw sites of every retained activation that meets the
inspection box belong to its doubled block box. -/
theorem raw_site_in_double_inspection_box (x y z : BlockSite) (N s : ℕ)
    (hs : 0 < s) (hsN : s ≤ N)
    (hy : y ∈ blockCube (fun d => x d-(N:ℤ)) (2*N+1))
    (hz : z ∈ blockCube (alignedCubeBase s (alignedCubeIndex s y)) s) :
    z ∈ blockCube (fun d => x d-2*(N:ℤ)) (4*N+1) := by
  intro d
  have hd := hy d
  have hdist := abs_lt.mp (same_aligned_cube_distance s hs y z hz d)
  change x d-(N:ℤ) ≤ y d ∧ y d < x d-(N:ℤ)+((2*N+1:ℕ):ℤ) at hd
  change x d-2*(N:ℤ) ≤ z d ∧ z d < x d-2*(N:ℤ)+((4*N+1:ℕ):ℤ)
  constructor <;> omega

/-- One actual physical block fits into the physical carrier of any discrete
block population containing its index. -/
theorem physical_block_region_subset (j : ℤ) (a z : BlockSite) (s : ℕ)
    (hz : z ∈ blockCube a s) :
    physicalBlockRegion j z 1 ⊆ physicalBlockRegion j a s := by
  intro p hp d
  have hd := hz d
  have hlow : (a d:ℝ) ≤ z d := by exact_mod_cast hd.1
  have hupperZ : z d+1 ≤ a d+(s:ℤ) := by omega
  have hupper : (z d:ℝ)+1 ≤ (a d:ℝ)+s := by exact_mod_cast hupperZ
  have hW := (physical_block_side_pos j).le
  have hl := mul_le_mul_of_nonneg_left hlow hW
  have hu := mul_le_mul_of_nonneg_left hupper hW
  have hp' := hp d
  norm_num only [Nat.cast_one] at hp'
  change physicalBlockSide j*(a d:ℝ)-(3:ℝ)^j/2 ≤ p d ∧
    p d ≤ physicalBlockSide j*((a d:ℝ)+s)-(3:ℝ)^j/2
  constructor <;> linarith only [hp'.1,hp'.2,hl,hu]

/-- The literal physical carrier of all retained observations for N=3^M. -/
def localizedPhysicalRegion (j : ℤ) (M : ℕ) (x : BlockSite) : Set (Vec 2) :=
  physicalBlockRegion j (fun d => x d-2*(3^M:ℤ)) (4*3^M+1)

theorem localized_physical_region_measurable (j : ℤ) (M : ℕ) (x : BlockSite) :
    MeasurableSet (localizedPhysicalRegion j M x) :=
  physical_block_region_measurable _ _ _

/-- A site in the inspection box has its complete physical block carrier
inside the doubled source observation region. -/
theorem inspection_block_physical_subset (j : ℤ) (M : ℕ) (x y : BlockSite)
    (hy : y ∈ blockCube (fun d => x d-((3^M:ℕ):ℤ)) (2*3^M+1)) :
    physicalBlockRegion j y 1 ⊆ localizedPhysicalRegion j M x := by
  have hN : 0 < (3^M:ℕ) := by positivity
  have hh := raw_site_in_double_inspection_box x y y (3^M) 1 (by norm_num) hN hy
    (mem_own_aligned_cube 1 (by norm_num) y)
  exact physical_block_region_subset j _ y _ hh

end
end ASDExplicitGamma.Inverse
