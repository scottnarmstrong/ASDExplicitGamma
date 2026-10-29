module

public import ASDExplicitGamma.Inverse.WeightedLocalizationVolumeWeights

/-! Literal two-by-two blocks in the source's root-relative fine grid. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory

/-- Two-by-two fine cells, translated with the actual root and with the
half-fine-cell offset of the triadic cube grid. -/
noncomputable def localizationBlockSet (Q : TriadicCube 2) (R : ℕ) (z : Fin 2 → ℤ) : Set (Vec 2) :=
  Set.pi Set.univ (fun i => Set.Ico
    (cubeCenter Q i + (2 * (z i : ℝ) - 1 / 2) * cubeScaleFactor (originCube 2 (Q.scale - R)))
    (cubeCenter Q i + (2 * (z i : ℝ) + 3 / 2) * cubeScaleFactor (originCube 2 (Q.scale - R))))

/-- The root-relative fine mesh has strictly positive physical side. -/
theorem localization_block_fine_scale_pos (Q : TriadicCube 2) (R : ℕ) :
    0 < cubeScaleFactor (originCube 2 (Q.scale - R)) :=
  zpow_pos (by norm_num) _

/-- Their exact area is four fine-square areas, with no dimension loss. -/
theorem localization_block_volume (Q : TriadicCube 2) (R : ℕ) (z : Fin 2 → ℤ) :
    volume (localizationBlockSet Q R z) =
      ENNReal.ofReal (4 * (cubeScaleFactor (originCube 2 (Q.scale - R))) ^ 2) := by
  rw [localizationBlockSet, Real.volume_pi_Ico]
  have he (i : Fin 2) :
      (cubeCenter Q i + (2 * (z i : ℝ) + 3 / 2) * cubeScaleFactor (originCube 2 (Q.scale - R))) -
      (cubeCenter Q i + (2 * (z i : ℝ) - 1 / 2) * cubeScaleFactor (originCube 2 (Q.scale - R))) =
        2 * cubeScaleFactor (originCube 2 (Q.scale - R)) := by ring
  simp_rw [he]
  rw [Fin.prod_univ_two, ← ENNReal.ofReal_mul (mul_nonneg (by norm_num)
    (localization_block_fine_scale_pos Q R).le)]
  congr 1
  ring

/-- Actual block area relative to the physical root is 4*3^(-2R). -/
theorem localization_block_volume_ratio (Q : TriadicCube 2) (R : ℕ) (z : Fin 2 → ℤ) :
    (volume (localizationBlockSet Q R z)).toReal / (volume (cubeSet Q)).toReal =
      4 * (1 / 9 : ℝ) ^ R := by
  rw [localization_block_volume, ENNReal.toReal_ofReal (by positivity), volume_cubeSet_toReal,
    cubeVolume_eq_pow_scale]
  have hs : cubeScaleFactor (originCube 2 (Q.scale - R)) = (3 : ℝ) ^ Q.scale / (3 : ℝ) ^ R := by
    rw [cubeScaleFactor]
    change (3 : ℝ) ^ (Q.scale - (R : ℤ)) = _
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
  rw [hs, one_div_pow]
  have hp : (9 : ℝ) ^ R = (3 : ℝ) ^ R * (3 : ℝ) ^ R := by rw [← mul_pow]; norm_num
  rw [hp]
  field_simp

end ASDExplicitGamma.Inverse
