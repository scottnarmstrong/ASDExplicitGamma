module

public import ASDExplicitGamma.Inverse.ContainedTriangleArea
public import Algsuperdiff.Section3.Provider.Multiscale.SimplexDomains

/-! The contained cubes at the open variational domain carrier. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Multiscale

/-- The open contained cube is contained in the actual open simplex domain. -/
theorem triangle_contained_open_cube (l : ℤ) (pi : Equiv.Perm (Fin 2)) (n : ℕ)
    {R : TriadicCube 2} (hR : R ∈ triangleContainedCubes l pi n) :
    openCubeSet R ⊆ ({supportCube := originCube 2 l, order := pi} : Whitney.KuhnCell 2).openCarrier := by
  obtain ⟨hRd, hRo⟩ := Finset.mem_filter.mp hR
  intro x hx
  apply Whitney.KuhnCell.mem_openCarrier_iff.mpr
  refine ⟨openCubeSet_subset_of_mem_descendantsAtDepth hRd hx, ?_⟩
  intro i j hij
  have hi : i = 0 := Fin.ext (by omega)
  have hj : j = 1 := Fin.ext (by omega)
  subst i; subst j
  change Whitney.triadicLocalCoordinate (originCube 2 l) x (pi 0) <
    Whitney.triadicLocalCoordinate (originCube 2 l) x (pi 1)
  simp only [Whitney.triadicLocalCoordinate, originCube, Pi.zero_apply, Int.cast_zero, zero_mul, sub_zero]
  have hs : 0 < cubeScaleFactor R := zpow_pos (by norm_num) _
  have hidx : (R.index (pi 0) : ℝ) + 1 ≤ (R.index (pi 1) : ℝ) := by
    exact_mod_cast (show R.index (pi 0) + 1 ≤ R.index (pi 1) by omega)
  have hm := mul_le_mul_of_nonneg_right hidx hs.le
  have hp := (hx (pi 0)).2
  have hq := (hx (pi 1)).1
  change x (pi 0) < ((R.index (pi 0) : ℝ) + 1 / 2) * cubeScaleFactor R at hp
  change ((R.index (pi 1) : ℝ) - 1 / 2) * cubeScaleFactor R < x (pi 1) at hq
  linarith only [hp, hq, hm]

/-- Open cube domains exhaust the actual open triangle up to a null set. -/
theorem triangle_open_partition_cover_ae (l : ℤ) (pi : Equiv.Perm (Fin 2)) :
    ({supportCube := originCube 2 l, order := pi} : Whitney.KuhnCell 2).openCarrier =ᵐ[volume]
      ⋃ R ∈ triangleCubePartition l pi, openCubeSet R := by
  let T : Whitney.KuhnCell 2 := ⟨originCube 2 l, pi⟩
  have hT : T.carrier =ᵐ[volume] T.openCarrier := by
    apply ae_eq_set.mpr
    exact ⟨volume_carrier_diff_openCarrier T,
      by rw [Set.sdiff_eq_empty.mpr T.openCarrier_subset_carrier, measure_empty]⟩
  have hU : (⋃ R ∈ triangleCubePartition l pi, cubeSet R) =ᵐ[volume]
      ⋃ R ∈ triangleCubePartition l pi, openCubeSet R := by
    filter_upwards [ae_all_iff.mpr (fun R : TriadicCube 2 => cubeSet_ae_eq_openCubeSet R)] with x hx
    apply propext
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨R, hR, hxR⟩
      exact ⟨R, hR, by rwa [← hx R]⟩
    · rintro ⟨R, hR, hxR⟩
      exact ⟨R, hR, by rwa [hx R]⟩
  exact hT.symm.trans ((triangle_partition_cover_ae l pi).trans hU)

end ASDExplicitGamma.Inverse
