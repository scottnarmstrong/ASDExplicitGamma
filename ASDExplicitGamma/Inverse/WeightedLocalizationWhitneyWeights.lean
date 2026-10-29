module

public import ASDExplicitGamma.Inverse.WeightedLocalizationBlockGeometry
public import ASDExplicitGamma.Inverse.WeightedLocalizationCentering
public import ASDExplicitGamma.Inverse.WhitneyRootTranslation

/-! Exact partial-block masses on the literal translated Whitney source layers. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory

/-- The deterministic layer used before selected-height substitution. -/
def localizationWhitneyLayer (Q : TriadicCube 2) (H n : ℕ) : Set (Vec 2) :=
  ⋃ P ∈ bankWhitneyLayer Q.scale H (n + 1), translateSet (triadicCubeShift Q) (cubeSet P)

/-- Source layer measurability is obtained from the actual translated cubes. -/
theorem localization_whitney_layer_measurable (Q : TriadicCube 2) (H n : ℕ) :
    MeasurableSet (localizationWhitneyLayer Q H n) := by
  apply MeasurableSet.iUnion
  intro P
  apply MeasurableSet.iUnion
  intro _hP
  rw [← preimage_subRight_eq_translateSet]
  exact (measurableSet_cubeSet P).preimage (measurable_id.sub_const _)

/-- The complete physical layer lies inside its actual root. -/
theorem localization_whitney_layer_subset (Q : TriadicCube 2) (H n : ℕ) :
    localizationWhitneyLayer Q H n ⊆ cubeSet Q := by
  intro x hx
  obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.mp hx
  rw [mem_translateSet_iff_sub_mem] at hxP
  rw [cubeSet_eq_translateSet_originCube_of_triadicCube, mem_translateSet_iff_sub_mem]
  exact openCubeSet_subset_cubeSet _ (whitney_interior Q.scale H ⟨n + 1, hP⟩ hxP)

/-- The layer's actual physical volume is exactly the corrected source weight. -/
theorem localization_whitney_layer_volume (Q : TriadicCube 2) (H n : ℕ) :
    (volume (localizationWhitneyLayer Q H n)).toReal / (volume (cubeSet Q)).toReal = bankLayerWeight n := by
  have hd : (↑(bankWhitneyLayer Q.scale H (n + 1)) : Set (TriadicCube 2)).PairwiseDisjoint
      (fun P => translateSet (triadicCubeShift Q) (cubeSet P)) := by
    intro P hP R hR hne
    exact whitney_translated_disjoint Q H ⟨n + 1, hP⟩ ⟨n + 1, hR⟩ hne
  have hm (P : TriadicCube 2) : MeasurableSet (translateSet (triadicCubeShift Q) (cubeSet P)) := by
    rw [← preimage_subRight_eq_translateSet]
    exact (measurableSet_cubeSet P).preimage (measurable_id.sub_const _)
  have hv := measureReal_biUnion_finset (μ := volume) hd (fun P _ => hm P)
    (fun P _ => by rw [volume_translateSet_eq]; exact (volume_cubeSet_lt_top P).ne)
  change (volume (⋃ P ∈ bankWhitneyLayer Q.scale H (n + 1),
    translateSet (triadicCubeShift Q) (cubeSet P))).toReal = _ at hv
  change (volume (⋃ P ∈ bankWhitneyLayer Q.scale H (n + 1),
    translateSet (triadicCubeShift Q) (cubeSet P))).toReal / _ = _
  rw [hv]
  exact whitney_root_layer_volume_fraction Q H n

end ASDExplicitGamma.Inverse
