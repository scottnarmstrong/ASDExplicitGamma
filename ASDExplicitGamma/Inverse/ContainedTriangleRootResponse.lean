module

public import ASDExplicitGamma.Inverse.ContainedTriangleTranslation

/-! Full physical response comparison for every translated source triangle. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Homogenization.Book
open Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Multiscale

/-- All actual root-relative contained cube domains are disjoint. -/
theorem triangle_root_cubes_disjoint (Q : TriadicCube 2) (pi : Equiv.Perm (Fin 2)) :
    Pairwise (fun P R : ↥(triangleCubePartition Q.scale pi) =>
      Disjoint (openCubeSet (triangleRootCube Q pi P))
        (openCubeSet (triangleRootCube Q pi R))) := by
  intro P R hne
  rw [triangleRootCube, triangleRootCube, root_translated_open_cube_set,
    root_translated_open_cube_set]
  apply Set.disjoint_left.mpr
  intro x hxP hxR
  rw [mem_translateSet_iff_sub_mem] at hxP hxR
  exact Set.disjoint_left.mp (triangle_partition_disjoint Q.scale pi P.2 R.2
    (fun he => hne (Subtype.ext he)))
    (openCubeSet_subset_cubeSet _ hxP) (openCubeSet_subset_cubeSet _ hxR)

/-- The complete translated family exhausts its actual open triangle. -/
theorem triangle_root_cubes_cover (Q : TriadicCube 2) (pi : Equiv.Perm (Fin 2)) :
    volume ((Whitney.KuhnCell.mk Q pi).openCarrier \
      ⋃ P : ↥(triangleCubePartition Q.scale pi), openCubeSet (triangleRootCube Q pi P)) = 0 := by
  have he : (Whitney.KuhnCell.mk Q pi).openCarrier \
      (⋃ P : ↥(triangleCubePartition Q.scale pi), openCubeSet (triangleRootCube Q pi P)) =
      translateSet (triadicCubeShift Q)
        ((Whitney.KuhnCell.mk (originCube 2 Q.scale) pi).openCarrier \
          ⋃ P : ↥(triangleCubePartition Q.scale pi), openCubeSet P.1) := by
    ext x
    rw [triangle_open_translate]
    simp only [Set.mem_sdiff, Set.mem_iUnion, mem_translateSet_iff_sub_mem]
    simp_rw [triangleRootCube, root_translated_open_cube_set, mem_translateSet_iff_sub_mem]
  rw [he, volume_translateSet_eq]
  simpa only [Set.iUnion_subtype] using
    (ae_eq_set.mp (triangle_open_partition_cover_ae Q.scale pi)).1

/-- Each contained cube uses the original triangle coefficient, restricted
internally with its unchanged physical representative. -/
noncomputable def triangleRootCubeCoeff (Q : TriadicCube 2) (pi : Equiv.Perm (Fin 2))
    (a : Ch02.CoeffOn (kuhnCellDomain ⟨Q, pi⟩))
    (P : ↥(triangleCubePartition Q.scale pi)) :
    Ch02.CoeffOn (Ch02.cubeDomain (triangleRootCube Q pi P)) :=
  restrictCoeffOn a (triangle_root_cube_subset Q pi P)

/-- Full variational response comparison at every physical selected triangle,
summed over the entire contained-cube family with its true volume weights. -/
theorem triangle_root_full_response_le (Q : TriadicCube 2) (pi : Equiv.Perm (Fin 2))
    (a : Ch02.CoeffOn (kuhnCellDomain ⟨Q, pi⟩)) (p q : Vec 2) :
    ENNReal.ofReal (blockVecDot (p, q) (blockMatVecMul
      (Ch02.coarseBlockMatrix (kuhnCellDomain ⟨Q, pi⟩) a) (p, q))) ≤
      ∑' P : ↥(triangleCubePartition Q.scale pi), ENNReal.ofReal
        (((volume (openCubeSet (triangleRootCube Q pi P))).toReal /
          (volume (kuhnCellDomain ⟨Q, pi⟩ : Set (Vec 2))).toReal) *
          blockVecDot (p, q) (blockMatVecMul
            (Ch02.coarseBlockMatrix (Ch02.cubeDomain (triangleRootCube Q pi P))
              (triangleRootCubeCoeff Q pi a P)) (p, q))) := by
  exact Whitney.ofReal_bfA_quadratic_le_simplex_weighted_tsum a (triangleRootCubeCoeff Q pi a)
    (fun _ => rfl) (triangle_root_cube_subset Q pi) (triangle_root_cubes_disjoint Q pi)
    (triangle_root_cubes_cover Q pi)
    p q (fun _ => p) (fun _ => q) (fun _ => p) (fun _ => q)
    (by simpa using (Whitney.potentialZeroTraceFieldOn_zero
      (U := (kuhnCellDomain ⟨Q, pi⟩ : Set (Vec 2)))))
    (by simpa using (Whitney.solenoidalZeroNormalTraceFieldOn_zero
      (U := (kuhnCellDomain ⟨Q, pi⟩ : Set (Vec 2)))))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)

end ASDExplicitGamma.Inverse
