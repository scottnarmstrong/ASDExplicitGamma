module

public import ASDExplicitGamma.Cold.NativeCellIndex
public import ASDExplicitGamma.Cold.ColdHistoryCaps

/-! # The actual complete native depth-history cell arrays, including negative lags -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Algsuperdiff.Section3
open scoped ENNReal
namespace ASDExplicitGamma.Cold

/-- Every actual depth-r cell of the native parent at lag j, indexed without truncating r. -/
def coldNativeHistoryCell (m : ℤ) (j r : ℕ) (i : Fin (9^r)) : TriadicCube 2 :=
  (coldCellEquiv (originCube 2 (m+(j:ℤ))) r i).val

/-- The complete actual depth-r trace array in the one fixed old coefficient/frame. -/
def coldNativeHistoryArray (M : ABKModel 2) (m : ℤ) (j r : ℕ) (i : Fin (9^r)) : Cutoff.CutoffSample 2 → ℝ :=
  coldNativeCellTrace M m (coldNativeHistoryCell m j r i)

theorem coldNativeHistoryCell_scale (m : ℤ) (j r : ℕ) (i : Fin (9^r)) :
    (coldNativeHistoryCell m j r i).scale = m+(j:ℤ)-(r:ℤ) :=
  scale_eq_sub_of_mem_descendantsAtDepth (coldCellEquiv (originCube 2 (m+(j:ℤ))) r i).property

/-- Every actual history cell has the exact integer-scale origin trace law. -/
theorem coldNativeHistoryArray_sameLaw (M : ABKModel 2) (m : ℤ) (j r : ℕ) (i : Fin (9^r)) :
    ProbabilityTheory.IdentDistrib (coldNativeHistoryArray M m j r i) (cutoffTraceDefect M m (m+(j:ℤ)-(r:ℤ)))
      (Cutoff.cutoffSampleLaw M).toMeasure (Cutoff.cutoffSampleLaw M).toMeasure := by
  simpa only [coldNativeHistoryArray,coldNativeHistoryCell_scale] using
    coldNativeCellTrace_identDistrib M m (coldNativeHistoryCell m j r i)

/-- The raw prefix uses the genuine nonnegative native lag j-r. -/
theorem coldNativeHistoryArray_prefix_sameLaw (M : ABKModel 2) (m : ℤ) (j r : ℕ)
    (hr : r ≤ j) (i : Fin (9^r)) :
    ProbabilityTheory.IdentDistrib (coldNativeHistoryArray M m j r i) (coldNativeTrace M m (j-r))
      (Cutoff.cutoffSampleLaw M).toMeasure (Cutoff.cutoffSampleLaw M).toMeasure := by
  have he : m+(j:ℤ)-(r:ℤ) = m+((j-r:ℕ):ℤ) := by omega
  simpa only [he,coldNativeTrace] using coldNativeHistoryArray_sameLaw M m j r i

/-- The complete fine tail at r=k+j uses exactly the frozen strong20 cell m-k. -/
theorem coldNativeHistoryArray_fine_sameLaw (M : ABKModel 2) (m : ℤ) (j k : ℕ) (i : Fin (9^(k+j))) :
    ProbabilityTheory.IdentDistrib (coldNativeHistoryArray M m j (k+j) i) (cutoffTraceDefect M m (m-(k:ℤ)))
      (Cutoff.cutoffSampleLaw M).toMeasure (Cutoff.cutoffSampleLaw M).toMeasure := by
  have he : m+(j:ℤ)-((k+j:ℕ):ℤ) = m-(k:ℤ) := by omega
  simpa only [he] using coldNativeHistoryArray_sameLaw M m j (k+j) i

/-- Every actual history cell, without a depth restriction, has a finite twentieth moment. -/
theorem coldNativeHistoryArray_memLp {M : ABKModel 2} {m : ℤ} {R S : ℝ}
    (hroot : root20 M m ≤ ENNReal.ofReal R) (hstrong : strong20 M m ≤ ENNReal.ofReal S)
    (j r : ℕ) (i : Fin (9^r)) : MemLp (coldNativeHistoryArray M m j r i) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  by_cases hr : r ≤ j
  · exact (coldNativeHistoryArray_prefix_sameLaw M m j r hr i).memLp_iff.mpr (coldNativeTrace_memLp hroot (j-r))
  · have hex : ∃ k, r = k+j := ⟨r-j,by omega⟩
    obtain ⟨k,rfl⟩ := hex
    exact (coldNativeHistoryArray_fine_sameLaw M m j k i).memLp_iff.mpr (cold_native_fine_memLp hstrong k)

end ASDExplicitGamma.Cold
