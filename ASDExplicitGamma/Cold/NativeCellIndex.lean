module

public import ASDExplicitGamma.Cold.NativeFourColor
public import ASDExplicitGamma.Cold.NativeTraceMoments

/-! # Literal finite indexing of actual native cell partitions -/

@[expose] public section
noncomputable section
open Homogenization Algsuperdiff.Section3
namespace ASDExplicitGamma.Cold

/-- The actual depth-r partition has exactly 9^r cells. -/
theorem cold_square_cells_card (Q : TriadicCube 2) (r : ℕ) : Fintype.card (SquareCells Q r) = 9^r := by
  simp only [SquareCells,Fintype.card_coe,descendantsAtDepth_card]
  norm_num

/-- A finite reindexing of the actual descendant cells, with no replacement of the partition. -/
def coldCellEquiv (Q : TriadicCube 2) (r : ℕ) : Fin (9^r) ≃ SquareCells Q r :=
  (Fintype.equivFinOfCardEq (cold_square_cells_card Q r)).symm

/-- The actual child cell at parent lag ell and cell lag k. -/
def coldNativeChildCell (m : ℤ) (k ell : ℕ) (i : Fin (9^(ell-k))) : TriadicCube 2 :=
  (coldCellEquiv (originCube 2 (m+(ell:ℤ))) (ell-k) i).val

/-- Every valid child lag is the literal native scale m+k. -/
theorem coldNativeChildCell_scale (m : ℤ) {k ell : ℕ} (hk : k ≤ ell) (i : Fin (9^(ell-k))) :
    (coldNativeChildCell m k ell i).scale = m+(k:ℤ) := by
  have he := scale_eq_sub_of_mem_descendantsAtDepth
    (coldCellEquiv (originCube 2 (m+(ell:ℤ))) (ell-k) i).property
  change (coldNativeChildCell m k ell i).scale = m+(ell:ℤ)-((ell-k:ℕ):ℤ) at he
  omega

/-- Distinct finite child indices are distinct actual cell cubes. -/
theorem coldNativeChildCell_injective (m : ℤ) (k ell : ℕ) : Function.Injective (coldNativeChildCell m k ell) := by
  intro i j hij
  apply (coldCellEquiv (originCube 2 (m+(ell:ℤ))) (ell-k)).injective
  exact Subtype.ext hij

end ASDExplicitGamma.Cold
