module

public import ASDExplicitGamma.Inverse.HistoryOperator
public import ASDExplicitGamma.Inverse.HistoryTraceMonotone
public import ASDExplicitGamma.Triadic.HistoryMonotoneENNReal

/-! IN-HISTORY-CONVERSION: normalized u=1/8 and raw u=1/4 histories,
with the completed cutoff, root n-40, sample law, and true frame fixed throughout. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

noncomputable def bufferRawOperatorHistory (M : ABKModel 2) (n : ℤ)
    (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  ∑' r : ℕ, ENNReal.ofReal ((3:ℝ)^(-(1/2:ℝ)*r))*bufferOperatorMax M n r ω

noncomputable def historyRawFactor : ℝ := (1-(3:ℝ)^(-(1/2:ℝ)))⁻¹

theorem history_raw_factor_pos : 0 < historyRawFactor := by
  unfold historyRawFactor
  apply inv_pos.mpr
  have h := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ)<3) (by norm_num : -(1/2:ℝ)<0)
  linarith only [h]

/-- The source gamma range removes theta from the normalized budget. -/
theorem buffer_operator_history_L12_absolute (M : ABKModel 2) (n : ℤ)
    (hgmax : M.gamma ≤ gammaZero)
    (hcap : buffer40History M n ≤ ENNReal.ofReal (61/10*theta M)) :
    eLpNorm (bufferOperatorHistory M n) 12 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (61/10:ℝ) := by
  have hg0 : (0:ℝ) < gammaZero := by norm_num [gammaZero]
  have ht1 : theta M ≤ 1 := (div_le_one hg0).mpr hgmax
  apply (buffer_operator_history_L12 M n hcap).trans
  apply ENNReal.ofReal_le_ofReal
  linarith only [ht1]

end ASDExplicitGamma.Inverse
