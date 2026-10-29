module

public import ASDExplicitGamma.Inverse.ContainedTriangleResponse
public import ASDExplicitGamma.Inverse.WhitneyRootTranslation

/-! Translation of the actual triangle and its contained triadic cubes. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3.Provider

/-- The open triangle at an arbitrary support cube is its literal physical translate. -/
theorem triangle_open_translate (Q : TriadicCube 2) (pi : Equiv.Perm (Fin 2)) :
    (Whitney.KuhnCell.mk Q pi).openCarrier = translateSet (triadicCubeShift Q)
      (Whitney.KuhnCell.mk (originCube 2 Q.scale) pi).openCarrier := by
  ext x
  rw [mem_translateSet_iff_sub_mem, Whitney.KuhnCell.mem_openCarrier_iff,
    Whitney.KuhnCell.mem_openCarrier_iff, openCubeSet_eq_translateSet_originCube_of_triadicCube Q,
    mem_translateSet_iff_sub_mem]
  have he (i : Fin 2) : Whitney.triadicLocalCoordinate Q x i =
      Whitney.triadicLocalCoordinate (originCube 2 Q.scale) (x - triadicCubeShift Q) i := by
    simp only [Whitney.triadicLocalCoordinate, triadicCubeShift, cubeScaleFactor,
      originCube, Pi.zero_apply, Int.cast_zero, zero_mul, sub_zero, Pi.sub_apply]
  simp_rw [he]

/-- A translated finer cube also represents the exact translated open domain. -/
theorem root_translated_open_cube_set (Q : TriadicCube 2)
    (P : {P : TriadicCube 2 // P.scale ≤ Q.scale}) :
    openCubeSet (rootTranslatedCube Q P) = translateSet (triadicCubeShift Q) (openCubeSet P.1) := by
  have hpow : (3 : ℝ) ^ (Q.scale - P.1.scale).toNat * (3 : ℝ) ^ P.1.scale =
      (3 : ℝ) ^ Q.scale := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    omega
  have he : (fun i : Fin 2 =>
      ((descendantTranslationShift (Q.scale - P.1.scale).toNat Q.index i : ℤ) : ℝ) *
        cubeScaleFactor P.1) = triadicCubeShift Q := by
    funext i
    simp only [descendantTranslationShift, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
      triadicCubeShift, cubeScaleFactor]
    calc
      _ = (Q.index i : ℝ) * ((3 : ℝ) ^ (Q.scale - P.1.scale).toNat * (3 : ℝ) ^ P.1.scale) := by ring
      _ = _ := by rw [hpow]
  ext x
  change x ∈ openCubeSet (translateCube _ P.1) ↔ _
  rw [mem_openCubeSet_translateCube_iff, mem_translateSet_iff_sub_mem, he]

/-- The exact source depth relation of every first-contained cube. -/
theorem triangle_partition_scale (l : ℤ) (pi : Equiv.Perm (Fin 2))
    {P : TriadicCube 2} (hP : P ∈ triangleCubePartition l pi) :
    ∃ n : ℕ, P ∈ triangleFirstCubes l pi n ∧ P.scale = l - ((n + 1 : ℕ) : ℤ) := by
  obtain ⟨n, hn⟩ := hP
  exact ⟨n, hn, scale_eq_sub_of_mem_descendantsAtDepth
    (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1⟩

/-- Actual root-relative triadic cube assigned to each member of the full triangle dissection. -/
def triangleRootCube (Q : TriadicCube 2) (pi : Equiv.Perm (Fin 2))
    (P : ↥(triangleCubePartition Q.scale pi)) : TriadicCube 2 :=
  rootTranslatedCube Q ⟨P.1, by
    obtain ⟨n, _, hn⟩ := triangle_partition_scale Q.scale pi P.2
    omega⟩

/-- Every translated variational cube stays inside its actual support triangle. -/
theorem triangle_root_cube_subset (Q : TriadicCube 2) (pi : Equiv.Perm (Fin 2))
    (P : ↥(triangleCubePartition Q.scale pi)) :
    openCubeSet (triangleRootCube Q pi P) ⊆ (Whitney.KuhnCell.mk Q pi).openCarrier := by
  rw [triangleRootCube, root_translated_open_cube_set, triangle_open_translate]
  intro x hx
  rw [mem_translateSet_iff_sub_mem] at hx ⊢
  exact triangle_cube_domain_subset Q.scale pi P hx

end ASDExplicitGamma.Inverse
