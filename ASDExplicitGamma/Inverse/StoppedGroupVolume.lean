module

public import ASDExplicitGamma.Inverse.WhitneyRootLayerCarrier

/-! Actual two-layer support volume of a source midpoint mesh group. The
bound is used for H1 summability; it does not replace the exact source
weights in the response or density budgets. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section

def rootGroupSupport (Q : TriadicCube 2) (H a : ℕ) : Set (Vec 2) :=
  rootLayerCarrier Q H a ∪ rootLayerCarrier Q H (a+1)

def rootGroupVolumeBudget (Q : TriadicCube 2) (a : ℕ) : ℝ :=
  16*(volume (cubeSet Q)).toReal*(1/3:ℝ)^a

theorem root_group_support_measurable (Q : TriadicCube 2) (H a : ℕ) :
    MeasurableSet (rootGroupSupport Q H a) :=
  (root_layer_carrier_measurable Q H a).union (root_layer_carrier_measurable Q H (a+1))

theorem root_group_support_subset_open (Q : TriadicCube 2) (H a : ℕ) :
    rootGroupSupport Q H a ⊆ openCubeSet Q :=
  Set.union_subset (root_layer_carrier_subset_open Q H a) (root_layer_carrier_subset_open Q H (a+1))

theorem root_group_volume_budget_nonneg (Q : TriadicCube 2) (a : ℕ) :
    0 ≤ rootGroupVolumeBudget Q a := by unfold rootGroupVolumeBudget; positivity

theorem root_group_support_volume_le (Q : TriadicCube 2) (H a : ℕ) :
    (volume (rootGroupSupport Q H a)).toReal ≤ rootGroupVolumeBudget Q a := by
  have hu := measureReal_union_le (μ := (volume : Measure (Vec 2)))
    (rootLayerCarrier Q H a) (rootLayerCarrier Q H (a+1))
  have h0 := root_layer_carrier_volume_le Q H a
  have h1 := root_layer_carrier_volume_le Q H (a+1)
  rw [pow_succ] at h1
  have hp := mul_nonneg (ENNReal.toReal_nonneg : 0 ≤ (volume (cubeSet Q)).toReal)
    (show 0 ≤ (1/3:ℝ)^a by positivity)
  change _ ≤ 16*(volume (cubeSet Q)).toReal*(1/3:ℝ)^a
  change (volume (rootGroupSupport Q H a)).toReal ≤ _ at hu
  change (volume (rootGroupSupport Q H a)).toReal ≤
    (volume (rootLayerCarrier Q H a)).toReal + (volume (rootLayerCarrier Q H (a+1))).toReal at hu
  nlinarith only [hu,h0,h1,hp]

/-- The actual spatial support measure in the parent H1 space has the
finite source volume budget, with its restriction intersection discharged. -/
theorem root_group_support_restrict_measure_le (Q : TriadicCube 2) (H a : ℕ) :
    (volume.restrict (openCubeSet Q)) (rootGroupSupport Q H a) ≤
      ENNReal.ofReal (rootGroupVolumeBudget Q a) := by
  rw [Measure.restrict_apply (root_group_support_measurable Q H a),
    Set.inter_eq_left.mpr (root_group_support_subset_open Q H a)]
  have hfin : volume (rootGroupSupport Q H a) ≠ ∞ :=
    measure_ne_top_of_subset ((root_group_support_subset_open Q H a).trans (openCubeSet_subset_cubeSet Q))
      (volume_cubeSet_lt_top Q).ne
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal (root_group_support_volume_le Q H a)

end
end ASDExplicitGamma.Inverse
