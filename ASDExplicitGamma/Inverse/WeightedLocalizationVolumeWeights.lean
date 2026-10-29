module

public import ASDExplicitGamma.Inverse.WhitneyLayerMass

/-! Actual partial-block volume weights of deterministic source layers. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory

/-- Physical volume of a partial block relative to the source root. -/
noncomputable def localizationPartialWeight (Q : TriadicCube 2) (E B : Set (Vec 2)) : ℝ :=
  (volume (E ∩ B)).toReal / (volume (cubeSet Q)).toReal

/-- Every actual partial-block weight is nonnegative. -/
theorem localization_partial_weight_nonneg (Q : TriadicCube 2) (E B : Set (Vec 2)) :
    0 ≤ localizationPartialWeight Q E B := by
  exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- A partial block's physical weight is bounded by its whole-block volume. -/
theorem localization_partial_weight_le (Q : TriadicCube 2) (E B : Set (Vec 2))
    (hB : volume B ≠ ⊤) :
    localizationPartialWeight Q E B ≤ (volume B).toReal / (volume (cubeSet Q)).toReal := by
  exact div_le_div_of_nonneg_right
    (ENNReal.toReal_mono hB (measure_mono Set.inter_subset_right)) ENNReal.toReal_nonneg

/-- Exact physical mass of all partial blocks. No upper bound on the layer
fraction is substituted for its actual value. -/
theorem localization_partial_weights_sum {ι : Type*} [Fintype ι]
    (Q : TriadicCube 2) (E : Set (Vec 2)) (hE : MeasurableSet E) (hEQ : E ⊆ cubeSet Q)
    (B : ι → Set (Vec 2)) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j))) (hcover : E ⊆ ⋃ i, B i) :
    (∑ i, localizationPartialWeight Q E (B i)) =
      (volume E).toReal / (volume (cubeSet Q)).toReal := by
  have he : E = ⋃ i, E ∩ B i := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
      exact Set.mem_iUnion.mpr ⟨i, hx, hi⟩
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact hi.1
  have hd : Pairwise (fun i j => Disjoint (E ∩ B i) (E ∩ B j)) := by
    intro i j hij
    exact (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right
  have hs := measureReal_iUnion_fintype (μ := volume) hd (fun i => hE.inter (hB i))
    (fun i => measure_ne_top_of_subset (Set.inter_subset_left.trans hEQ) (volume_cubeSet_lt_top Q).ne)
  rw [← he] at hs
  change (volume E).toReal = ∑ i, (volume (E ∩ B i)).toReal at hs
  change (∑ i, (volume (E ∩ B i)).toReal / (volume (cubeSet Q)).toReal) = _
  rw [← Finset.sum_div, ← hs]

end ASDExplicitGamma.Inverse
