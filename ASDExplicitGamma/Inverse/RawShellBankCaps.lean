module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import ASDExplicitGamma.Inverse.FullResponseProfile

/-! Finite-`p` adapters for the two exact order-128 bank inputs.
The full-response profile is deliberately named locally so this module can be
proved before the bank theorem. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory
open scoped ENNReal

/-- The source's order-128 full-response cap at band length `h`. -/
noncomputable def rawTraceFullResponseCap (gamma : ℝ) (h : ℕ) : ℝ :=
  4 * ((1009309 : ℝ) / 500000 + gamma *
    ((32474 : ℝ) * ((h + 1 : ℕ) : ℝ) + 11483216)) *
      (3 : ℝ) ^ ((2 * (h : ℝ) + 4) * gamma)

/-- The name for the order-128 full-response profile is exactly the
attenuated profile exported by the full-response arithmetic interface. -/
theorem raw_trace_full_response_cap_eq_profile (gamma : ℝ) (h : ℕ) :
    rawTraceFullResponseCap gamma h = fullResponseAttenuatedOutwardProfile gamma h := by
  simp only [rawTraceFullResponseCap, fullResponseAttenuatedOutwardProfile]
  norm_num

/-- Lower the exact OLD local-inverse order-128 bank cap to the order
`3p = 60` required by the finite-`p` raw-trace estimate. -/
theorem raw_trace_local_inverse_L60_of_L128
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Ω → ℝ) (hB : AEStronglyMeasurable B μ)
    (hcap : eLpNorm B (128 : ℝ≥0∞) μ ≤ ENNReal.ofReal (3683 / 2500 : ℝ)) :
    eLpNorm B (60 : ℝ≥0∞) μ ≤ ENNReal.ofReal (3683 / 2500 : ℝ) := by
  have hmonoRaw := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (f := B) (μ := μ) (p := 60) (q := 128) (by norm_num) hB
  have hmono : eLpNorm B (60 : ℝ≥0∞) μ ≤ eLpNorm B (128 : ℝ≥0∞) μ := by
    simpa only [measure_univ, ENNReal.one_rpow, mul_one] using hmonoRaw
  exact hmono.trans hcap

end ASDExplicitGamma.Inverse
