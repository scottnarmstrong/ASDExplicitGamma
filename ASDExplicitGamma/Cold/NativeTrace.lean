module

public import ASDExplicitGamma.Variational.TrueFrame
public import ASDExplicitGamma.Statements.OrdinaryMean
public import ASDExplicitGamma.Statements.Root20
public import ASDExplicitGamma.Statements.Strong20
public import ASDExplicitGamma.Cold.HistoryParameters

/-! # Actual fixed-label trace observables and native input caps -/

@[expose] public section
noncomputable section
open MeasureTheory Algsuperdiff.Section3 Homogenization
open scoped ENNReal
namespace ASDExplicitGamma.Cold

/-- The genuine trace at a nonnegative lag, with coefficient and true frame both frozen at m. -/
def coldNativeTrace (M : ABKModel 2) (m : ℤ) (ell : ℕ) : Cutoff.CutoffSample 2 → ℝ :=
  cutoffTraceDefect M m (m+(ell:ℤ))

/-- Actual trace means, with no induction-state label in the lag variable. -/
def coldNativeMean (M : ABKModel 2) (m : ℤ) (ell : ℕ) : ℝ :=
  ∫ ω, coldNativeTrace M m ell ω ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- Every fixed-label trace at every integer scale is integrable on the genuine sample space. -/
theorem integrable_cutoffTraceDefect (M : ABKModel 2) (m n : ℤ) :
    Integrable (cutoffTraceDefect M m n) (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hi := Variational.integrable_traceDefect_cutoffLaw M m (originCube 2 n) (Annealed.sigmaBar M m:ℝ)
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hi
  exact hi.comp_measurable (Cutoff.measurable_coefficientCutoff M.nu m)

/-- The fixed-label lag observable is measurable. -/
theorem coldNativeTrace_measurable (M : ABKModel 2) (m : ℤ) (ell : ℕ) :
    Measurable (coldNativeTrace M m ell) := Variational.cutoffTraceDefect_measurable M m _

/-- Actual fixed-label lag traces are nonnegative. -/
theorem coldNativeTrace_nonneg (M : ABKModel 2) (m : ℤ) (ell : ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ coldNativeTrace M m ell ω := Variational.cutoffTraceDefect_nonneg M m _ ω

/-- The frozen ordinaryMean cap is exactly a cap on the ordinary integral at lag zero. -/
theorem coldNativeMean_zero_le {M : ABKModel 2} {m : ℤ} {a : ℝ}
    (ha : 0 ≤ a) (hmean : ordinaryMean M m ≤ ENNReal.ofReal a) : coldNativeMean M m 0 ≤ a := by
  have hi := integrable_cutoffTraceDefect M m m
  have hn : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, 0 ≤ cutoffTraceDefect M m m ω :=
    Filter.Eventually.of_forall (Variational.cutoffTraceDefect_nonneg M m m)
  have he : coldNativeMean M m 0 = (ordinaryMean M m).toReal := by
    simpa only [coldNativeMean,coldNativeTrace,Int.natCast_zero,add_zero,ordinaryMean] using
      integral_eq_lintegral_of_nonneg_ae hn hi.aestronglyMeasurable
  rw [he]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmean).trans_eq (ENNReal.toReal_ofReal ha)

/-- The frozen root20 input supplies actual L20 membership at lag zero. -/
theorem coldNativeTrace_zero_memLp {M : ABKModel 2} {m : ℤ} {R : ℝ}
    (hroot : root20 M m ≤ ENNReal.ofReal R) :
    MemLp (coldNativeTrace M m 0) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  apply lt_top_iff_ne_top.mpr
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  simpa only [coldNativeTrace,Int.natCast_zero,add_zero,root20] using hroot

/-- The frozen root20 cap is also the ordinary real L20 cap consumed by the cold estimates. -/
theorem coldNativeTrace_zero_norm_le {M : ABKModel 2} {m : ℤ} {R : ℝ}
    (hR : 0 ≤ R) (hroot : root20 M m ≤ ENNReal.ofReal R) :
    lpNorm (coldNativeTrace M m 0) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ R := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hroot
  simpa only [lpNorm,root20,coldNativeTrace,Int.natCast_zero,add_zero,ENNReal.toReal_ofReal hR] using h

end ASDExplicitGamma.Cold
