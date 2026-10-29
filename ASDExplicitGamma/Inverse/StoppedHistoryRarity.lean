module

public import ASDExplicitGamma.Inverse.StoppedHistoryRaw
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

/-! Markov rarity for the actual raw history on every translated fine cube. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

/-- The literal old-history bad event has the source twelfth-power budget. -/
theorem stopped_cell_raw_history_tail (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (hQ : Q.scale = n-40) (hgmax : M.gamma ≤ gammaZero)
    (hcap : buffer40History M n ≤ ENNReal.ofReal (61/10*theta M))
    (τ : ℝ) (hτ : 0 < τ) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real
      {ω | ENNReal.ofReal τ < clippedCellRawHistory M n Q ω} ≤ (3*(61/10:ℝ)/τ)^12 := by
  have hm := meas_ge_le_mul_pow_eLpNorm_enorm (Cutoff.cutoffSampleLaw M).toMeasure
    (p := 12) (f := clippedCellRawHistory M n Q) (by norm_num) (by norm_num)
    (ENNReal.ofReal_ne_zero_iff.mpr hτ) (by simp)
  have hn := stopped_cell_raw_history_L12 M n Q hQ hgmax hcap
  have hb : (Cutoff.cutoffSampleLaw M).toMeasure
      {ω | ENNReal.ofReal τ < clippedCellRawHistory M n Q ω} ≤
      ENNReal.ofReal ((3*(61/10:ℝ)/τ)^12) := by
    simp only [enorm_eq_self, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] at hm
    have hsub : {ω | ENNReal.ofReal τ < clippedCellRawHistory M n Q ω} ⊆
        {ω | ENNReal.ofReal τ ≤ clippedCellRawHistory M n Q ω} :=
      by
        intro ω hω
        change ENNReal.ofReal τ < clippedCellRawHistory M n Q ω at hω
        exact le_of_lt hω
    apply (measure_mono hsub).trans
    apply hm.trans
    calc
      _ ≤ (ENNReal.ofReal τ)⁻¹^12 * (ENNReal.ofReal (3*(61/10:ℝ)))^12 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left' hn 12) (zero_le : (0:ℝ≥0∞) ≤ _)
      _ = ENNReal.ofReal ((3*(61/10:ℝ)/τ)^12) := by
        rw [← mul_pow, ← ENNReal.ofReal_inv_of_pos hτ,
          ← ENNReal.ofReal_mul (inv_nonneg.mpr hτ.le), ← ENNReal.ofReal_pow (by positivity)]
        congr 1
        ring
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (by positivity)] at hr
  exact hr

end ASDExplicitGamma.Inverse
