module

public import ASDExplicitGamma.Inverse.StoppedHistoryNorm
public import ASDExplicitGamma.Inverse.HistoryConversion

/-! The exact raw old-history conversion on every actual translated fine cube. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The source raw normalization payment is below three. -/
theorem stopped_history_raw_factor_le_three : historyRawFactor ≤ 3 := by
  have hroot : (3/2:ℝ) ≤ Real.sqrt 3 :=
    (Real.le_sqrt (by norm_num : (0:ℝ) ≤ 3/2) (by norm_num : (0:ℝ) ≤ 3)).mpr (by norm_num)
  have hq : (Real.sqrt 3)⁻¹ ≤ (2/3:ℝ) := by
    convert one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 3/2) hroot using 1 <;> norm_num [one_div]
  have hpow : (3:ℝ)^(-(1/2:ℝ)) = (Real.sqrt 3)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3),← Real.sqrt_eq_rpow]
  unfold historyRawFactor
  rw [hpow]
  have hh : (1/3:ℝ) ≤ 1-(Real.sqrt 3)⁻¹ := by linarith only [hq]
  convert one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/3) hh using 1 <;> norm_num [one_div]

/-- The actual raw operator history is bounded pointwise by the monotone
normalized trace history on that same translated cube and true cutoff frame. -/
theorem stopped_cell_raw_history_le (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    clippedCellRawHistory M n Q ω ≤ ENNReal.ofReal historyRawFactor*stoppedCellTraceHistory M n Q ω := by
  have hq : (0:ℝ) < (3:ℝ)^(-(1/4:ℝ)) := by positivity
  have hq1 : (3:ℝ)^(-(1/4:ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hq2 : ((3:ℝ)^(-(1/4:ℝ)))^2 = (3:ℝ)^(-(1/2:ℝ)) := by
    rw [Triadic.history_rpow_weight]
    norm_num
  have hgeo := Triadic.geometric_history_raw_le_ennreal _ hq hq1
    (fun r => stoppedCellTraceMax M n Q r ω) (stopped_cell_trace_max_monotone M n Q ω)
  rw [hq2] at hgeo
  simp only [Triadic.history_rpow_weight] at hgeo
  apply le_trans ?_ hgeo
  apply ENNReal.tsum_le_tsum
  intro r
  apply mul_le_mul_of_nonneg_left _ (zero_le : (0:ℝ≥0∞) ≤ _)
  unfold historyFiniteMax stoppedCellTraceMax
  apply Finset.sup_le
  intro R hR
  exact (ENNReal.ofReal_le_ofReal (history_operator_defect_le_trace M n R ω)).trans
    (Finset.le_sup (f := fun S => ENNReal.ofReal (historyTrace M n S ω)) hR)

/-- The source L12 raw-history budget at every translated fine root, derived
from the ordinary protected mixed native history coordinate alone. -/
theorem stopped_cell_raw_history_L12 (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2)
    (hQ : Q.scale = n-40) (hgmax : M.gamma ≤ gammaZero)
    (hcap : buffer40History M n ≤ ENNReal.ofReal (61/10*theta M)) :
    eLpNorm (clippedCellRawHistory M n Q) 12 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (3*(61/10:ℝ)) := by
  have hnorm : eLpNorm (clippedCellRawHistory M n Q) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal historyRawFactor*buffer40History M n := by
    have hm : eLpNorm (clippedCellRawHistory M n Q) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
        eLpNorm (fun ω => ENNReal.ofReal historyRawFactor*stoppedCellTraceHistory M n Q ω) 20
          (Cutoff.cutoffSampleLaw M).toMeasure := by
      apply eLpNorm_mono_enorm_ae (clipped_cell_raw_history_measurable M n Q).aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun ω => by simpa only [enorm_eq_self] using stopped_cell_raw_history_le M n Q ω)
    rw [history_constant_mul_L20 _ _ _ (stopped_cell_trace_history_measurable M n Q)] at hm
    exact hm.trans (mul_le_mul_of_nonneg_left (stopped_cell_trace_history_L20 M n Q hQ) (zero_le : (0:ℝ≥0∞) ≤ _))
  apply (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (12:ℝ≥0∞) ≤ 20)).trans
  apply hnorm.trans
  apply le_trans (mul_le_mul_of_nonneg_left hcap (zero_le : (0:ℝ≥0∞) ≤ _))
  rw [← ENNReal.ofReal_mul history_raw_factor_pos.le]
  apply ENNReal.ofReal_le_ofReal
  have hg0 : (0:ℝ) < gammaZero := by norm_num [gammaZero]
  have ht : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le hg0.le
  have ht1 : theta M ≤ 1 := (div_le_one hg0).mpr hgmax
  calc
    _ ≤ 3*(61/10*theta M) := mul_le_mul_of_nonneg_right stopped_history_raw_factor_le_three (by positivity)
    _ ≤ 3*(61/10:ℝ) := by nlinarith only [ht1]

end
end ASDExplicitGamma.Inverse
