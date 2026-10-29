module

public import ASDExplicitGamma.Cold.NativeGraphData
public import ASDExplicitGamma.Cold.NativeParentMoment
public import ASDExplicitGamma.Cold.OldGraphGlobal
public import ASDExplicitGamma.Cold.ColdGraphAnalytic

/-! # Both branches of the old graph candidate on the genuine native model -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix Algsuperdiff.Section3
open scoped ENNReal
namespace ASDExplicitGamma.Cold

/-- The actual native graph satisfies both old branches from genuine scalar child caps. -/
theorem cold_native_graph_old (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (Q : TriadicCube 2) (depth : ℕ) (hm : m ≤ Q.scale-(depth:ℤ)) {D L : ℝ}
    (hTA : MemLp (coldNativeCellTrace M m Q) 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hT : ∀ C : SquareCells Q depth, MemLp (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hD : ∀ C : SquareCells Q depth, (∫ ω, coldNativeCellTrace M m C.val ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ D)
    (hL : ∀ C : SquareCells Q depth, lpNorm (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ L) :
    2*(∫ ω, matrixFrobeniusSq (coldNativeResponse M m Q ω-1) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      coldOldGraphCap D L depth := by
  let G := coldNativeGraphData M h hM m Q depth hm hTA hT hD hL
  have hi : Nonempty (SquareCells Q depth) := inferInstance
  obtain ⟨C0⟩ := hi
  have hDorigin : (∫ ω, cutoffTraceDefect M m (Q.scale-depth) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ D := by
    have hh := hD C0
    rw [coldNativeCellTrace_integral,scale_eq_sub_of_mem_descendantsAtDepth C0.property] at hh
    exact hh
  have hmeanparent := (coldNativeCellTrace_mean_subadditive M m Q depth).trans hDorigin
  have htraceparent := coldNativeCellTrace_two_le_children M m Q depth hT hL
  have hmA : (∫ ω, (coldNativeResponse M m Q ω).trace-4 ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ D := by
    simpa only [coldNativeResponse_trace] using hmeanparent
  have htA : lpNorm (fun ω => (coldNativeResponse M m Q ω).trace-4) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ L := by
    simpa only [coldNativeResponse_trace] using htraceparent
  exact cold_old_graph_cap _ _ depth G.hA G.hX G.hp G.hq G.hD
    (Filter.Eventually.of_forall (coldNativeResponseAverage_subadditive M m Q depth))
    (Filter.Eventually.of_forall (coldNativeResponse_posDef M m Q))
    (Filter.Eventually.of_forall (coldNativeResponse_duality M m Q)) G.hmeanX hmA htA G.hcenter G.htraceX

end ASDExplicitGamma.Cold
