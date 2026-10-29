module

public import ASDExplicitGamma.Inverse.ContainedTriangleMass

/-! Exact normalization by the area of the actual half-open Kuhn triangle. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3.Provider

/-- Distinct first-containment depths have disjoint physical unions. -/
theorem triangle_layers_disjoint (l : ℤ) (pi : Equiv.Perm (Fin 2)) :
    Pairwise (fun n m : ℕ => Disjoint
      (⋃ R ∈ triangleFirstCubes l pi n, cubeSet R)
      (⋃ S ∈ triangleFirstCubes l pi m, cubeSet S)) := by
  intro n m hnm
  apply Set.disjoint_iUnion₂_left.mpr
  intro R hR
  apply Set.disjoint_iUnion₂_right.mpr
  intro S hS
  apply triangle_partition_disjoint l pi ⟨n, hR⟩ ⟨m, hS⟩
  intro he
  have hr := scale_eq_sub_of_mem_descendantsAtDepth
    (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1
  have hs := scale_eq_sub_of_mem_descendantsAtDepth
    (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  rw [he] at hr
  exact hnm (by omega)

/-- A planar Kuhn triangle has exactly half the area of its support square. -/
theorem triangle_area (l : ℤ) (pi : Equiv.Perm (Fin 2)) :
    (volume ({supportCube := originCube 2 l, order := pi} : Whitney.KuhnCell 2).carrier).toReal =
      (volume (cubeSet (originCube 2 l))).toReal / 2 := by
  have hu : (⋃ R ∈ triangleCubePartition l pi, cubeSet R) =
      ⋃ n : ℕ, ⋃ R ∈ triangleFirstCubes l pi n, cubeSet R := by
    ext x
    simp only [Set.mem_iUnion, triangleCubePartition, Set.mem_ofPred_eq]
    aesop
  rw [measure_congr (triangle_partition_cover_ae l pi), hu,
    measure_iUnion (triangle_layers_disjoint l pi)
      (fun n => MeasurableSet.iUnion fun R => MeasurableSet.iUnion fun _ => measurableSet_cubeSet R),
    ENNReal.tsum_toReal_eq (fun n => measure_ne_top_of_subset
      (by
        intro x hx
        obtain ⟨R, hR, hxR⟩ := Set.mem_iUnion₂.mp hx
        exact cubeSet_subset_of_mem_descendantsAtDepth
          (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1 hxR)
      (volume_cubeSet_lt_top (originCube 2 l)).ne)]
  simp_rw [triangle_first_volume]
  have hh := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num : (1 / 3 : ℝ) < 1)).mul_left
      ((volume (cubeSet (originCube 2 l))).toReal / 3)
  convert hh.tsum_eq using 1
  · congr 1
    funext n
    rw [pow_succ (1 / 3 : ℝ) n]
    ring
  · ring

/-- Exact normalized first-containment law P(I=n+1)=2*3^(-n-1). -/
theorem triangle_first_area_fraction (l : ℤ) (pi : Equiv.Perm (Fin 2)) (n : ℕ) :
    (∑ R ∈ triangleFirstCubes l pi n, (volume (cubeSet R)).toReal) /
      (volume ({supportCube := originCube 2 l, order := pi} : Whitney.KuhnCell 2).carrier).toReal =
        2 * (1 / 3 : ℝ) ^ (n + 1) := by
  rw [triangle_area]
  have hh := triangle_first_mass l pi n
  simp_rw [cubeMassRatio_eq_volume_ratio] at hh
  rw [← Finset.sum_div] at hh
  rw [div_div_eq_mul_div, mul_comm _ (2 : ℝ), mul_div_assoc, hh]

end ASDExplicitGamma.Inverse
