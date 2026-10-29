module

public import ASDExplicitGamma.Cold.NativeGraphTraceAverage

/-! # Ordinary mean and variance of the actual child trace average -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix Algsuperdiff.Section3
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- The full actual averaged trace is in L2. -/
theorem coldNativeResponseAverage_trace_memLp (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (r : ℕ)
    (hT : ∀ C : SquareCells Q r, MemLp (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure) :
    MemLp (fun ω => (coldNativeResponseAverage M m Q r ω).trace-4) 2 (Cutoff.cutoffSampleLaw M).toMeasure := by
  simp_rw [coldNativeResponseAverage_trace]
  exact (memLp_finsetSum Finset.univ (fun C _ => hT C)).const_mul _

/-- The full actual averaged trace has exactly the ordinary origin child mean. -/
theorem coldNativeResponseAverage_trace_mean (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (r : ℕ) :
    (∫ ω, (coldNativeResponseAverage M m Q r ω).trace-4 ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ ω, cutoffTraceDefect M m (Q.scale-r) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  simp_rw [coldNativeResponseAverage_trace]
  rw [integral_squareCellMean Q r (fun C => coldNativeCellTrace_integrable M m C.val)]
  have hh (C : SquareCells Q r) :
      (∫ ω, coldNativeCellTrace M m C.val ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
        ∫ ω, cutoffTraceDefect M m (Q.scale-r) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [coldNativeCellTrace_integral,scale_eq_sub_of_mem_descendantsAtDepth C.property]
  simp_rw [hh]
  exact squareCellMean_const Q r _

/-- The genuine child trace variance has the exact squared four-colour charge. -/
theorem cold_native_trace_average_variance (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (Q : TriadicCube 2) (r : ℕ) (hm : m ≤ Q.scale-(r:ℤ)) {L : ℝ}
    (hT : ∀ C : SquareCells Q r, MemLp (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hL : ∀ C : SquareCells Q r, lpNorm (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ L) :
    ProbabilityTheory.variance (fun ω => (coldNativeResponseAverage M m Q r ω).trace-4)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ (2*(3:ℝ)^(-(r:ℝ))*L)^2 := by
  let X := fun ω => (coldNativeResponseAverage M m Q r ω).trace-4
  let μprob := (Cutoff.cutoffSampleLaw M).toMeasure
  have hX := coldNativeResponseAverage_trace_memLp M m Q r hT
  have hh := cold_native_trace_average_center M h hM m Q r hm hT hL
  rw [← coldNativeResponseAverage_trace_mean M m Q r] at hh
  have hc : MemLp (fun ω => X ω-∫ a, X a ∂μprob) 2 μprob := hX.sub (memLp_const _)
  have hs := (sq_le_sq₀ (lpNorm_nonneg (f := fun ω => X ω-∫ a, X a ∂μprob) (p := 2) (μ := μprob))
    (lpNorm_nonneg.trans hh)).mpr hh
  rw [ASDExplicitGamma.Gaussian.rio_lpNorm_two_sq hc] at hs
  rwa [ProbabilityTheory.variance_eq_integral hX.aestronglyMeasurable.aemeasurable]

/-- The raw child average costs its exact mean plus its sharp centered fluctuation. -/
theorem cold_native_trace_average_raw (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (Q : TriadicCube 2) (r : ℕ) (hm : m ≤ Q.scale-(r:ℤ)) {D L : ℝ}
    (hT : ∀ C : SquareCells Q r, MemLp (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hL : ∀ C : SquareCells Q r, lpNorm (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ L)
    (hD : (∫ ω, cutoffTraceDefect M m (Q.scale-r) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ D) :
    lpNorm (fun ω => (coldNativeResponseAverage M m Q r ω).trace-4) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ D+2*(3:ℝ)^(-(r:ℝ))*L := by
  let μprob := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := fun ω => (coldNativeResponseAverage M m Q r ω).trace-4
  let μ := ∫ a, cutoffTraceDefect M m (Q.scale-r) a ∂μprob
  have hX := coldNativeResponseAverage_trace_memLp M m Q r hT
  have hc : MemLp (fun ω => X ω-μ) 2 μprob := hX.sub (memLp_const μ)
  have hh := cold_native_trace_average_center M h hM m Q r hm hT hL
  have ht := lpNorm_add_le hc (g := fun _ => μ) (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have he : (fun ω => X ω-μ)+(fun _ => μ) = X := by funext ω; simp only [Pi.add_apply,sub_add_cancel]
  rw [he,lpNorm_const' (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ⊤)] at ht
  have hn : 0 ≤ μ := integral_nonneg (Variational.cutoffTraceDefect_nonneg M m _)
  simp only [Real.norm_eq_abs,abs_of_nonneg hn,probReal_univ,Real.one_rpow,mul_one] at ht
  linarith only [ht,hh,hD]

end ASDExplicitGamma.Cold
