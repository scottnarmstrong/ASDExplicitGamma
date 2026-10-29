module

public import ASDExplicitGamma.Inverse.StoppedRootBlockPopulation

/-! Exact physical layer fractions on the globally indexed stopped-cluster blocks. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
noncomputable section

/-- Actual globally indexed buffered side at root-relative source resolution. -/
theorem root_physical_block_side (Q : TriadicCube 2) (R : ℕ) :
    physicalBlockSide (rootFineLabel Q R) =
      2*cubeScaleFactor (originCube 2 (Q.scale-R)) := by
  unfold physicalBlockSide rootFineLabel
  have he : Q.scale-(R:ℤ)-40+40 = Q.scale-R := by omega
  rw [he]
  rfl

/-- Area comparison uses only the side; the global and root-relative grids
need not have identical origins. -/
theorem root_physical_block_volume (Q : TriadicCube 2) (R : ℕ) (z : BlockSite) :
    volume (physicalBlockSet (rootFineLabel Q R) z) =
      volume (localizationBlockSet Q R z) := by
  rw [physical_block_set_volume,root_physical_block_side,localization_block_volume]
  congr 1
  ring

/-- The actual physical block's exact relative area is four fine-square areas. -/
theorem root_physical_block_volume_ratio (Q : TriadicCube 2) (R : ℕ) (z : BlockSite) :
    (volume (physicalBlockSet (rootFineLabel Q R) z)).toReal /
      (volume (cubeSet Q)).toReal = 4*(1/9:ℝ)^R := by
  rw [root_physical_block_volume]
  exact localization_block_volume_ratio Q R z

/-- The source maximum weight holds on the actual q3 block grid. -/
theorem root_partial_weight_le (Q : TriadicCube 2) (E : Set (Vec 2)) (R : ℕ)
    (z : BlockSite) :
    localizationPartialWeight Q E (physicalBlockSet (rootFineLabel Q R) z) ≤
      9*(1/9:ℝ)^R := by
  have hh := localization_partial_weight_le Q E (physicalBlockSet (rootFineLabel Q R) z)
    (by rw [physical_block_set_volume]; exact ENNReal.ofReal_ne_top)
  rw [root_physical_block_volume_ratio] at hh
  exact hh.trans (by nlinarith only [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/9) R])

/-- All actual partial blocks sum to the exact physical layer fraction. -/
theorem root_partial_weights_sum (Q : TriadicCube 2) (E : Set (Vec 2))
    (hE : MeasurableSet E) (hEQ : E ⊆ cubeSet Q) (R : ℕ) :
    (∑ z : ↥(rootBlockPopulation Q R),
      localizationPartialWeight Q E (physicalBlockSet (rootFineLabel Q R) z.val)) =
        (volume E).toReal/(volume (cubeSet Q)).toReal := by
  apply localization_partial_weights_sum Q E hE hEQ
    (fun z : ↥(rootBlockPopulation Q R) => physicalBlockSet (rootFineLabel Q R) z.val)
    (fun z => physical_block_set_measurable _ z.val)
  · intro z z' hne
    exact physical_block_sets_disjoint _ (fun he => hne (Subtype.ext he))
  · exact hEQ.trans (root_block_population_cover Q R)

/-- The actual layer fraction lies in the unit interval, with no profile bound. -/
theorem root_layer_fraction_bounds (Q : TriadicCube 2) (E : Set (Vec 2))
    (hEQ : E ⊆ cubeSet Q) :
    0 ≤ (volume E).toReal/(volume (cubeSet Q)).toReal ∧
    (volume E).toReal/(volume (cubeSet Q)).toReal ≤ 1 := by
  have hpos : 0 < (volume (cubeSet Q)).toReal := by
    rw [volume_cubeSet_toReal,cubeVolume_eq_pow_scale]
    positivity
  exact ⟨div_nonneg ENNReal.toReal_nonneg hpos.le,
    (div_le_one hpos).mpr (ENNReal.toReal_mono (volume_cubeSet_lt_top Q).ne (measure_mono hEQ))⟩

end
end ASDExplicitGamma.Inverse
