module

public import ASDExplicitGamma.Inverse.WhitneyRootLayerGeometry
public import ASDExplicitGamma.Inverse.WeightedLocalizationWhitneyWeights
public import Homogenization.Geometry.CubeMeasure

/-! Actual layer carriers, almost-everywhere interior coverage and valid
volume bounds for the finite-energy midpoint construction. Exact source
fractions are retained; the separate upper bound uses coefficient eight. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
open scoped ENNReal
noncomputable section

def rootLayerCarrier (Q : TriadicCube 2) (H n : ℕ) : Set (Vec 2) :=
  ⋃ P ∈ whitneyRootLayer Q H n, cubeSet P

theorem root_layer_carrier_measurable (Q : TriadicCube 2) (H n : ℕ) :
    MeasurableSet (rootLayerCarrier Q H n) :=
  MeasurableSet.iUnion (fun P => MeasurableSet.iUnion (fun _ => measurableSet_cubeSet P))

theorem root_layer_carrier_subset_open (Q : TriadicCube 2) (H n : ℕ) :
    rootLayerCarrier Q H n ⊆ openCubeSet Q := by
  intro x hx
  obtain ⟨P,hP,hxP⟩ := Set.mem_iUnion₂.mp hx
  rw [whitney_root_partition_cover Q H]
  exact Set.mem_iUnion₂.mpr ⟨P,(root_partition_iff_layer Q H P).mpr ⟨n,hP⟩,hxP⟩

theorem root_whitney_layer_zero (Q : TriadicCube 2) (H : ℕ) : whitneyRootLayer Q H 0 = ∅ := by
  simp only [whitneyRootLayer,bankWhitneyLayer,Whitney.whitneyLayer,show ¬1 ≤ (0:ℕ) by omega,ite_false,Finset.image_empty]

theorem root_whitney_layer_pos (Q : TriadicCube 2) (H n : ℕ) {P : TriadicCube 2}
    (hP : P ∈ whitneyRootLayer Q H n) : 1 ≤ n := by
  by_contra hn
  have hn0 : n=0 := by omega
  rw [hn0,root_whitney_layer_zero] at hP
  exact Finset.notMem_empty _ hP

theorem root_layer_carrier_zero (Q : TriadicCube 2) (H : ℕ) : rootLayerCarrier Q H 0 = ∅ := by
  simp only [rootLayerCarrier,root_whitney_layer_zero,Finset.notMem_empty,Set.iUnion_of_empty,Set.iUnion_empty]

/-- The finite actual translated-cell carrier is exactly the source layer
already used in the physical density and matrix averages. -/
theorem root_layer_carrier_eq_localization (Q : TriadicCube 2) (H n : ℕ) :
    rootLayerCarrier Q H (n+1) = localizationWhitneyLayer Q H n := by
  ext x
  constructor
  · intro hx
    obtain ⟨P,hP,hxP⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hP
    have hs := whitney_scale_le Q.scale H ⟨n+1,hR⟩
    change x ∈ cubeSet (rootTranslatedCube Q ⟨R,hs⟩) at hxP
    rw [root_translated_cube_set] at hxP
    exact Set.mem_iUnion₂.mpr ⟨R,hR,hxP⟩
  · intro hx
    obtain ⟨P,hP,hxP⟩ := Set.mem_iUnion₂.mp hx
    refine Set.mem_iUnion₂.mpr ⟨rootTranslateCube Q P,Finset.mem_image.mpr ⟨P,hP,rfl⟩,?_⟩
    have hs := whitney_scale_le Q.scale H ⟨n+1,hP⟩
    change x ∈ cubeSet (rootTranslatedCube Q ⟨P,hs⟩)
    rwa [root_translated_cube_set]

theorem root_layer_carrier_volume (Q : TriadicCube 2) (H n : ℕ) :
    (volume (rootLayerCarrier Q H (n+1))).toReal = bankLayerWeight n*(volume (cubeSet Q)).toReal := by
  have hv : (volume (cubeSet Q)).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal,cubeVolume_eq_pow_scale]
    positivity
  rw [root_layer_carrier_eq_localization]
  exact (div_eq_iff hv).mp (localization_whitney_layer_volume Q H n)

/-- Valid uniform upper bound used only for H1 summability. -/
theorem layer_weight_le_eight (n : ℕ) : bankLayerWeight n ≤ 8*(1/3:ℝ)^(n+1) := by
  cases n with
  | zero => norm_num [layerWeight_zero]
  | succ n =>
    rw [layerWeight_succ]
    exact sub_le_self _ (by positivity)

theorem root_layer_carrier_volume_le (Q : TriadicCube 2) (H n : ℕ) :
    (volume (rootLayerCarrier Q H n)).toReal ≤ 8*(1/3:ℝ)^n*(volume (cubeSet Q)).toReal := by
  cases n with
  | zero => rw [root_layer_carrier_zero]; simp only [measure_empty,ENNReal.toReal_zero]; positivity
  | succ n =>
    rw [root_layer_carrier_volume]
    exact mul_le_mul_of_nonneg_right (layer_weight_le_eight n) ENNReal.toReal_nonneg

/-- Almost every root point is in the interior of an actual Whitney cell;
every cell boundary is removed on one common null set. -/
theorem root_whitney_ae_interior_cover (Q : TriadicCube 2) (H : ℕ) :
    ∀ᵐ x ∂volume.restrict (openCubeSet Q), ∃ (n : ℕ) (P : TriadicCube 2),
      P ∈ whitneyRootLayer Q H n ∧ x ∈ openCubeSet P := by
  have he : ∀ᵐ x ∂(volume : Measure (Vec 2)), ∀ P : TriadicCube 2,
      x ∈ cubeSet P ↔ x ∈ openCubeSet P :=
    ae_all_iff.mpr (fun P => (cubeSet_ae_eq_openCubeSet P).mono (fun _ h => Iff.of_eq h))
  filter_upwards [ae_restrict_of_ae he,ae_restrict_mem (measurableSet_openCubeSet Q)] with x hxe hxQ
  rw [whitney_root_partition_cover Q H] at hxQ
  obtain ⟨P,hP,hxP⟩ := Set.mem_iUnion₂.mp hxQ
  obtain ⟨n,hn⟩ := (root_partition_iff_layer Q H P).mp hP
  exact ⟨n,P,hn,(hxe P).mp hxP⟩

end
end ASDExplicitGamma.Inverse
