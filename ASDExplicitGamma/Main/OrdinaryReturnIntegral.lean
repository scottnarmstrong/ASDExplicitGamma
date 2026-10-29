module

public import ASDExplicitGamma.Cold.NativeTrace

/-! Convert the actual nonnegative trace expectation to the native ENNReal mean. -/

@[expose] public section
noncomputable section

open MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

namespace ASDExplicitGamma.Main

/-- A real bound on the target-label fixed-frame trace expectation gives the
corresponding frozen `ordinaryMean` cap. Integrability is supplied by the
actual fixed-ν cutoff-law trace theorem, and the observable's nonnegativity is
pointwise; no separate conversion premise is retained. -/
theorem main_ordinary_mean_le_of_real_expectation
    (M : ABKModel 2) (n : ℤ) {a : ℝ}
    (hreal : (∫ ω, cutoffTraceDefect M n n ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ a) :
    ordinaryMean M n ≤ ENNReal.ofReal a := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let f : Cutoff.CutoffSample 2 → ℝ := cutoffTraceDefect M n n
  have hnonneg : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall fun ω =>
    Variational.cutoffTraceDefect_nonneg M n n ω
  have hmeas : AEStronglyMeasurable f μ := by
    exact (Variational.cutoffTraceDefect_measurable M n n).aestronglyMeasurable
  have hint : Integrable f μ := by
    exact ASDExplicitGamma.Cold.integrable_cutoffTraceDefect M n n
  have hfinite : ordinaryMean M n ≠ ∞ := by
    change (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ≠ ∞
    exact (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).2 hint
  have hrealEq : (∫ ω, f ω ∂μ) = (ordinaryMean M n).toReal := by
    simpa only [ordinaryMean, f, μ] using
      (integral_eq_lintegral_of_nonneg_ae hnonneg hmeas)
  have hmeanEq : ordinaryMean M n = ENNReal.ofReal (∫ ω, f ω ∂μ) := by
    calc
      ordinaryMean M n = ENNReal.ofReal ((ordinaryMean M n).toReal) :=
        (ENNReal.ofReal_toReal hfinite).symm
      _ = ENNReal.ofReal (∫ ω, f ω ∂μ) := by rw [← hrealEq]
  calc
    ordinaryMean M n = ENNReal.ofReal (∫ ω, f ω ∂μ) := hmeanEq
    _ ≤ ENNReal.ofReal a := ENNReal.ofReal_le_ofReal (by simpa [f, μ] using hreal)

end ASDExplicitGamma.Main

end
