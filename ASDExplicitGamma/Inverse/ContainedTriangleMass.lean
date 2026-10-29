module

public import ASDExplicitGamma.Inverse.ContainedTriangleNull
public import ASDExplicitGamma.Inverse.ContainedTriangleDisjoint
public import ASDExplicitGamma.Inverse.WhitneyLayerMass

/-! Physical area fractions of the complete planar triangle dissection. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3.Provider

/-- A first-contained depth n+1 layer occupies exactly 3^(-n-1) of its support square. -/
theorem triangle_first_mass (l : ℤ) (pi : Equiv.Perm (Fin 2)) (n : ℕ) :
    (∑ R ∈ triangleFirstCubes l pi n, Whitney.cubeMassRatio (originCube 2 l) R) =
      (1 / 3 : ℝ) ^ (n + 1) := by
  have he (R : TriadicCube 2) (hR : R ∈ triangleFirstCubes l pi n) :
      Whitney.cubeMassRatio (originCube 2 l) R = ((9 : ℝ) ^ (n + 1))⁻¹ := by
    have hs := scale_eq_sub_of_mem_descendantsAtDepth
      (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1
    rw [Whitney.cubeMassRatio, hs]
    change ((3 : ℝ) ^ 2) ^ (l - ((n + 1 : ℕ) : ℤ) - l) = _
    rw [show l - ((n + 1 : ℕ) : ℤ) - l = -((n + 1 : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast]
    norm_num
  rw [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul, triangle_first_card]
  push_cast
  rw [show (9 : ℝ) ^ (n + 1) = (3 : ℝ) ^ (n + 1) * (3 : ℝ) ^ (n + 1) by
    rw [← mul_pow]; norm_num]
  simp only [one_div, inv_pow, mul_inv, mul_inv_cancel_left₀ (pow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0))]

/-- The first-contained physical layer volume, with no normalization convention hidden. -/
theorem triangle_first_volume (l : ℤ) (pi : Equiv.Perm (Fin 2)) (n : ℕ) :
    (volume (⋃ R ∈ triangleFirstCubes l pi n, cubeSet R)).toReal =
      (volume (cubeSet (originCube 2 l))).toReal * (1 / 3 : ℝ) ^ (n + 1) := by
  have hd : (↑(triangleFirstCubes l pi n) : Set (TriadicCube 2)).PairwiseDisjoint cubeSet := by
    intro R hR S hS hne
    exact triangle_partition_disjoint l pi ⟨n, hR⟩ ⟨n, hS⟩ hne
  rw [show (volume (⋃ R ∈ triangleFirstCubes l pi n, cubeSet R)).toReal =
    ∑ R ∈ triangleFirstCubes l pi n, (volume (cubeSet R)).toReal from
      measureReal_biUnion_finset hd (fun R _ => measurableSet_cubeSet R)
        (fun R _ => (volume_cubeSet_lt_top R).ne)]
  have hh := triangle_first_mass l pi n
  simp_rw [cubeMassRatio_eq_volume_ratio] at hh
  rw [← Finset.sum_div] at hh
  exact (div_eq_iff (ne_of_gt (by
    rw [volume_cubeSet_toReal, cubeVolume_eq_pow_scale]
    positivity : 0 < (volume (cubeSet (originCube 2 l))).toReal))).mp hh |>.trans (mul_comm _ _)

end ASDExplicitGamma.Inverse
