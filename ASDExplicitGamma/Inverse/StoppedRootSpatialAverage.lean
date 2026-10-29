module

public import ASDExplicitGamma.Inverse.StoppedRootBlockWeights
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The finite partial-volume sum is the actual spatial average over a source layer. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
noncomputable section

/-- Exact finite partition identity for any scalar values on the actual blocks.
This is pointwise, including the global grid's half-open boundaries. -/
theorem root_layer_indicator_eq (Q : TriadicCube 2) (R : ℕ)
    (E : Set (Vec 2)) (hEQ : E ⊆ cubeSet Q) (F : BlockSite → ℝ) :
    E.indicator (fun p => F (physicalBlockIndex (rootFineLabel Q R) p)) =
      fun p => ∑ z : ↥(rootBlockPopulation Q R),
        (E ∩ physicalBlockSet (rootFineLabel Q R) z.val).indicator (fun _ => F z.val) p := by
  classical
  funext p
  by_cases hp : p ∈ E
  · let z : ↥(rootBlockPopulation Q R) :=
      ⟨physicalBlockIndex (rootFineLabel Q R) p,root_block_population_mem Q R p (hEQ hp)⟩
    rw [Set.indicator_of_mem hp]
    symm
    rw [Finset.sum_eq_single z]
    · have hz : p ∈ E ∩ physicalBlockSet (rootFineLabel Q R) z.val :=
        ⟨hp,physical_block_index_mem _ _⟩
      rw [Set.indicator_of_mem hz]
    · intro y _ hy
      apply Set.indicator_of_notMem
      intro hmem
      apply hy
      apply Subtype.ext
      exact ((physical_block_index_eq_iff _ _ _).mpr hmem.2).symm
    · simp only [Finset.mem_univ,not_true_eq_false,false_implies]
  · rw [Set.indicator_of_notMem hp]
    symm
    apply Finset.sum_eq_zero
    intro z _
    exact Set.indicator_of_notMem (fun hmem => hp hmem.1) _

/-- The actual spatial average equals the finite sum with the exact partial
weights. No regularity or integrability assumption on the block values is needed. -/
theorem root_spatial_average_eq (Q : TriadicCube 2) (R : ℕ)
    (E : Set (Vec 2)) (hE : MeasurableSet E) (hEQ : E ⊆ cubeSet Q) (F : BlockSite → ℝ) :
    (∫ p in E, F (physicalBlockIndex (rootFineLabel Q R) p)) /
      (volume (cubeSet Q)).toReal =
      ∑ z : ↥(rootBlockPopulation Q R),
        localizationPartialWeight Q E (physicalBlockSet (rootFineLabel Q R) z.val)*F z.val := by
  rw [← integral_indicator hE,root_layer_indicator_eq Q R E hEQ F]
  rw [integral_finsetSum]
  · simp_rw [integral_indicator_const _ (hE.inter (physical_block_set_measurable _ _)),
      smul_eq_mul]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro z _
    change (volume (E ∩ physicalBlockSet (rootFineLabel Q R) z.val)).toReal*F z.val /
      (volume (cubeSet Q)).toReal = _
    unfold localizationPartialWeight
    ring
  · intro z _
    apply (integrable_indicator_iff (hE.inter (physical_block_set_measurable _ _))).mpr
    exact integrableOn_const (measure_ne_top_of_subset
      (Set.inter_subset_left.trans hEQ) (volume_cubeSet_lt_top Q).ne)

end
end ASDExplicitGamma.Inverse
