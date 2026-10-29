module

public import ASDExplicitGamma.Cold.NativeGraphTraceMoment
public import ASDExplicitGamma.Cold.GraphMeanOrder

/-! # Proved actual matrix data shared by the two improved native graph candidates -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix Algsuperdiff.Section3
open scoped ENNReal
namespace ASDExplicitGamma.Cold

/-- The actual source and parent block means, with their proved source charges. -/
structure ColdNativeGraphData (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (depth : ℕ) (D L : ℝ) where
  p : ℝ
  q : ℝ
  r : ℝ
  s : ℝ
  hp : 0 ≤ p
  hq : 0 ≤ q
  hr : 0 ≤ r
  hs : 0 ≤ s
  hA : ∀ i j, MemLp (fun ω => coldNativeResponse M m Q ω i j) 2 (Cutoff.cutoffSampleLaw M).toMeasure
  hX : ∀ i j, MemLp (fun ω => coldNativeResponseAverage M m Q depth ω i j) 2 (Cutoff.cutoffSampleLaw M).toMeasure
  hmeanX : matrixMean (Cutoff.cutoffSampleLaw M).toMeasure (coldNativeResponseAverage M m Q depth) = 1+coldGraphBlockMean p q
  hmeanA : matrixMean (Cutoff.cutoffSampleLaw M).toMeasure (coldNativeResponse M m Q) = 1+coldGraphBlockMean r s
  hD : 2*(p+q) ≤ D
  hcenter : matrixFrobeniusL2 (Cutoff.cutoffSampleLaw M).toMeasure
    (fun ω => coldNativeResponseAverage M m Q depth ω-
      matrixMean (Cutoff.cutoffSampleLaw M).toMeasure (coldNativeResponseAverage M m Q depth)) ≤
        2*(3:ℝ)^(-(depth:ℝ))*Real.sqrt (2*D+L^2)
  hvariance : ProbabilityTheory.variance (fun ω => (coldNativeResponseAverage M m Q depth ω).trace-4)
    (Cutoff.cutoffSampleLaw M).toMeasure ≤ (2*(3:ℝ)^(-(depth:ℝ))*L)^2
  htraceX : lpNorm (fun ω => (coldNativeResponseAverage M m Q depth ω).trace-4) 2
    (Cutoff.cutoffSampleLaw M).toMeasure ≤ D+2*(3:ℝ)^(-(depth:ℝ))*L

/-- Construct all actual graph inputs from scalar cell moments and the genuine q3 model.
No graph estimate, independence or block-order premise is assumed. -/
def coldNativeGraphData (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (Q : TriadicCube 2) (depth : ℕ) (hm : m ≤ Q.scale-(depth:ℤ)) {D L : ℝ}
    (hTA : MemLp (coldNativeCellTrace M m Q) 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hT : ∀ C : SquareCells Q depth, MemLp (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hD : ∀ C : SquareCells Q depth, (∫ ω, coldNativeCellTrace M m C.val ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ D)
    (hL : ∀ C : SquareCells Q depth, lpNorm (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ L) :
    ColdNativeGraphData M m Q depth D L := by
  apply Classical.choice
  let μprob := (Cutoff.cutoffSampleLaw M).toMeasure
  obtain ⟨p,q,hp,hq,hmean⟩ := coldNativeResponse_mean_blocks M m (originCube 2 (Q.scale-depth))
  obtain ⟨r,s,hr,hs,hmeanA⟩ := coldNativeResponse_mean_blocks M m Q
  have hcell (C : SquareCells Q depth) := coldNativeResponse_memLp_of_trace M m C.val (hT C)
  have hX := coldNativeResponseAverage_memLp M m Q depth hcell
  have hmeanX : matrixMean μprob (coldNativeResponseAverage M m Q depth) = 1+coldGraphBlockMean p q :=
    (coldNativeResponseAverage_mean M m Q depth (fun C i j => (hcell C i j).integrable (by norm_num))).trans hmean
  have hi : Nonempty (SquareCells Q depth) := inferInstance
  obtain ⟨C0⟩ := hi
  have hcmean : matrixMean μprob (coldNativeResponse M m C0.val) = 1+coldGraphBlockMean p q := by
    rw [coldNativeResponse_cell_mean,scale_eq_sub_of_mem_descendantsAtDepth C0.property]
    exact hmean
  have htrace := cold_graph_mean_trace (coldNativeResponse M m C0.val)
    (fun i => (hcell C0 i i).integrable (by norm_num)) hcmean
  have hDb : 2*(p+q) ≤ D := by
    rw [← htrace]
    simpa only [coldNativeResponse_trace] using hD C0
  have hDorigin : (∫ ω, cutoffTraceDefect M m (Q.scale-depth) ω ∂μprob) ≤ D := by
    have hh := hD C0
    rw [coldNativeCellTrace_integral,scale_eq_sub_of_mem_descendantsAtDepth C0.property] at hh
    exact hh
  exact ⟨{
    p := p, q := q, r := r, s := s, hp := hp, hq := hq, hr := hr, hs := hs
    hA := coldNativeResponse_memLp_of_trace M m Q hTA
    hX := hX, hmeanX := hmeanX, hmeanA := hmeanA, hD := hDb
    hcenter := cold_native_response_average_center M h hM m Q depth hm hT hD hL
    hvariance := cold_native_trace_average_variance M h hM m Q depth hm hT hL
    htraceX := cold_native_trace_average_raw M h hM m Q depth hm hT hL hDorigin }⟩

end ASDExplicitGamma.Cold
