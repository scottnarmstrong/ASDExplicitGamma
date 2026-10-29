module

public import ASDExplicitGamma.Cold.NeumannSquare

/-! # Complete mixed sine/cosine Parseval on a square -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic ASDExplicitGamma.Triadic.Torus
open scoped BigOperators ENNReal

local instance instColdCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instColdCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

namespace ASDExplicitGamma.Cold

/-- Odd reflection changes the sign, but preserves the norm almost everywhere. -/
theorem square_oddSign_sq_ae :
    ∀ᵐ t : Fin 2 → UnitAddCircle, ∀ i : Fin 2, oddSign (t i) ^ 2 = 1 := by
  have hnull : volume {s : UnitAddCircle | oddSign s = 0} = 0 := by
    apply measure_mono_null (t := {0} ∪ {((1 / 2 : ℝ) : UnitAddCircle)})
    · intro s hs
      rcases oddSign_zero_rep_endpoint s hs with hzero | hhalf
      · left
        exact Set.mem_singleton_iff.mpr (by simpa [hzero] using (coe_rep s).symm)
      · right
        exact Set.mem_singleton_iff.mpr (by simpa [hhalf] using (coe_rep s).symm)
    · apply le_antisymm _ bot_le
      exact (measure_union_le _ _).trans (by simp [volume_singleton_unitAddCircle])
  rw [ae_all_iff]
  intro i
  have heval : volume {t : Fin 2 → UnitAddCircle | oddSign (t i) = 0} = 0 := by
    exact Measure.pi_eval_preimage_null (fun _ : Fin 2 => (volume : Measure UnitAddCircle)) hnull
  have hne : ∀ᵐ t : Fin 2 → UnitAddCircle, oddSign (t i) ≠ 0 := by
    simpa only [ae_iff, not_not] using heval
  filter_upwards [hne] with t ht
  exact oddSign_sq_eq_one_of_ne_zero (t i) ht

/-- Full mixed Parseval for an arbitrary choice of sine coordinates. -/
theorem square_mixed_parseval (Q : TriadicCube 2) (O : Finset (Fin 2)) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    HasSum (fun p : Fin 2 → ℤ =>
      (∫ x, boxMode (cubeCorner Q) (cubeScaleFactor Q) O p x * f x
        ∂normalizedCubeMeasure Q) ^ 2) (∫ x, f x ^ 2 ∂normalizedCubeMeasure Q) := by
  rw [← boxMeasure_eq_normalizedCubeMeasure] at hf ⊢
  have h := hasSum_sq_boxCoeff (cubeCorner Q) (cubeScaleFactor_pos' Q) O hf
  have heq : (∫ t,
      ((∏ i ∈ O, oddSign (t i)) * f (boxMap (cubeCorner Q) (cubeScaleFactor Q) t)) ^ 2) =
      ∫ x, f x ^ 2 ∂boxMeasure (cubeCorner Q) (cubeScaleFactor Q) := by
    rw [← integral_boxMap (cubeCorner Q) (cubeScaleFactor_pos' Q)
      (f := fun x => f x ^ 2) (hf.aestronglyMeasurable.pow 2)]
    apply integral_congr_ae
    filter_upwards [square_oddSign_sq_ae] with t ht
    rw [mul_pow, ← Finset.prod_pow]
    simp only [ht, Finset.prod_const_one, one_mul]
  rwa [heq] at h

end ASDExplicitGamma.Cold
