module

public import ASDExplicitGamma.Inverse.StoppedElementaryCubes

/-! The literal fine-to-buffered-block map, including negative lattice coordinates. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- The actual two-by-two buffer-block index of a fine triadic lattice site. -/
def fineBlockIndex (x : BlockSite) : BlockSite := fun d => x d/(2*3^40)

/-- A fine site lies in its block's exact integer interval. -/
theorem fine_block_index_bounds (x : BlockSite) (d : Fin 2) :
    (2*3^40:ℤ)*fineBlockIndex x d ≤ x d ∧
    x d < (2*3^40:ℤ)*(fineBlockIndex x d+1) := by
  have he := Int.emod_add_mul_ediv (x d) (2*3^40)
  have h0 := Int.emod_nonneg (x d) (by norm_num : (2*3^40:ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos (x d) (by norm_num : (0:ℤ) < 2*3^40)
  change (2*3^40:ℤ)*(x d/(2*3^40)) ≤ x d ∧
    x d < (2*3^40:ℤ)*(x d/(2*3^40)+1)
  constructor <;> omega

/-- A source fine 2-neighbor step maps to an equal or touching block. -/
theorem fine_block_index_neighbor (x y : BlockSite)
    (hxy : ∀ d, |y d-x d| ≤ 2) :
    ∀ d, |fineBlockIndex y d-fineBlockIndex x d| ≤ 1 := by
  intro d
  have hx := fine_block_index_bounds x d
  have hy := fine_block_index_bounds y d
  have hd := abs_le.mp (hxy d)
  rw [abs_le]
  constructor <;> norm_num at * <;> omega

/-- Endpoint displacement loses at most one block after division by the
source block side; this is the deterministic radius conversion. -/
theorem fine_block_endpoint_distance (x y : BlockSite) (d : Fin 2) :
    |y d-x d| < (2*3^40:ℤ)*(|fineBlockIndex y d-fineBlockIndex x d|+1) := by
  have hx := fine_block_index_bounds x d
  have hy := fine_block_index_bounds y d
  rcases le_total (fineBlockIndex x d) (fineBlockIndex y d) with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    rw [abs_lt]
    constructor <;> omega
  · rw [abs_of_nonpos (sub_nonpos.mpr h),neg_sub]
    rw [abs_lt]
    constructor <;> omega

end ASDExplicitGamma.Inverse
