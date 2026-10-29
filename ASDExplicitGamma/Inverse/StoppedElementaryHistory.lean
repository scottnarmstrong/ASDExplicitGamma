module

public import ASDExplicitGamma.Inverse.StoppedHistoryRarity
public import ASDExplicitGamma.Gaussian.WaveGateEnlargedFailure

/-! The exact parent-and-two-generation population of old-history failures. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian

/-- Each elementary fine cube keeps its own buffered old cutoff and true frame. -/
def elementaryHistoryFailure (M : ABKModel 2) (τ : ℝ)
    (Q : WavePlanarElementaryIndex → TriadicCube 2) : Set (Cutoff.CutoffSample 2) :=
  {ω | ∃ i, ENNReal.ofReal τ < clippedCellRawHistory M ((Q i).scale+40) (Q i) ω}

theorem elementary_history_failure_measurable (M : ABKModel 2) (τ : ℝ)
    (Q : WavePlanarElementaryIndex → TriadicCube 2) :
    MeasurableSet (elementaryHistoryFailure M τ Q) := by
  have hi (i : WavePlanarElementaryIndex) : MeasurableSet {ω : Cutoff.CutoffSample 2 |
      ENNReal.ofReal τ < clippedCellRawHistory M ((Q i).scale+40) (Q i) ω} :=
    measurableSet_lt measurable_const (clipped_cell_raw_history_measurable M _ _)
  simpa only [elementaryHistoryFailure,Set.iUnion_ofPred] using MeasurableSet.iUnion hi

/-- The enlarged zero mark pays exactly E_b times the raw twelfth-power tail. -/
theorem elementary_history_failure_probability (M : ABKModel 2) (hg : M.gamma ≤ gammaZero)
    (τ : ℝ) (hτ : 0 < τ) (Q : WavePlanarElementaryIndex → TriadicCube 2)
    (hcap : ∀ i, buffer40History M ((Q i).scale+40) ≤ ENNReal.ofReal (61/10*theta M)) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real (elementaryHistoryFailure M τ Q) ≤
      (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 := by
  let E (i : WavePlanarElementaryIndex) : Set (Cutoff.CutoffSample 2) :=
    {ω | ENNReal.ofReal τ < clippedCellRawHistory M ((Q i).scale+40) (Q i) ω}
  have hE (i : WavePlanarElementaryIndex) : (Cutoff.cutoffSampleLaw M).toMeasure.real (E i) ≤
      (3*(61/10:ℝ)/τ)^12 :=
    stopped_cell_raw_history_tail M _ _ (by omega) hg (hcap i) τ hτ
  calc
    _ ≤ ∑ i, (Cutoff.cutoffSampleLaw M).toMeasure.real (E i) := by
      simpa only [elementaryHistoryFailure,Set.iUnion_ofPred,E] using
        measureReal_iUnion_fintype_le (μ := (Cutoff.cutoffSampleLaw M).toMeasure) E
    _ ≤ ∑ _i : WavePlanarElementaryIndex, (3*(61/10:ℝ)/τ)^12 := Finset.sum_le_sum fun i _ => hE i
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,wave_planar_elementary_card,
        wavePlanarEventCount,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      ring

end ASDExplicitGamma.Inverse
