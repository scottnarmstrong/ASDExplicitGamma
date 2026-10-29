module

public import ASDExplicitGamma.Cold.NativeSubadditivity

/-! # Actual positive-lag trace moments from the native root input -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Algsuperdiff.Section3
open scoped ENNReal BigOperators
namespace ASDExplicitGamma.Cold

/-- All positive-lag native traces have finite twentieth moment by actual subadditivity
and the genuine root-cell law. No stochastic independence is needed for membership. -/
theorem coldNativeTrace_memLp {M : ABKModel 2} {m : ℤ} {R : ℝ}
    (hroot : root20 M m ≤ ENNReal.ofReal R) (ell : ℕ) :
    MemLp (coldNativeTrace M m ell) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  let Q := originCube 2 (m+(ell:ℤ))
  have hroot0 : MemLp (cutoffTraceDefect M m m) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
    simpa only [coldNativeTrace,Int.natCast_zero,add_zero] using coldNativeTrace_zero_memLp hroot
  have hcell (C : SquareCells Q ell) :
      MemLp (coldNativeCellTrace M m C.val) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
    apply (coldNativeCellTrace_memLp_iff M m C.val 20).mpr
    have hc : C.val.scale = m := by
      rw [scale_eq_sub_of_mem_descendantsAtDepth C.property]
      change m+(ell:ℤ)-(ell:ℤ) = m
      ring
    rw [hc]
    exact hroot0
  let A := fun ω => squareCellMean Q ell (fun C => coldNativeCellTrace M m C.val ω)
  have hA : MemLp A 20 (Cutoff.cutoffSampleLaw M).toMeasure :=
    (memLp_finsetSum Finset.univ (fun C _ => hcell C)).const_mul _
  have hAn (ω : Cutoff.CutoffSample 2) : 0 ≤ A ω := by
    have h := squareCellMean_mono Q ell (fun C => coldNativeCellTrace_nonneg M m C.val ω)
    rw [squareCellMean_const] at h
    exact h
  have hbound (ω : Cutoff.CutoffSample 2) : coldNativeTrace M m ell ω ≤ A ω :=
    coldNativeCellTrace_subadditive M m Q ell ω
  apply hA.of_le (coldNativeTrace_measurable M m ell).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (coldNativeTrace_nonneg M m ell ω),abs_of_nonneg (hAn ω)]
  exact hbound ω

end ASDExplicitGamma.Cold
