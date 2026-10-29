module

public import ASDExplicitGamma.Cold.NativeMatchedFamily
public import ASDExplicitGamma.Cold.TraceHistoryMonotone
public import ASDExplicitGamma.Cold.SquareCellMean

/-! # Actual native trace subadditivity and monotone lag means -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Algsuperdiff.Section3
namespace ASDExplicitGamma.Cold

/-- Every genuine translated-cell trace has finite ordinary expectation. -/
theorem coldNativeCellTrace_integrable (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) :
    Integrable (coldNativeCellTrace M m Q) (Cutoff.cutoffSampleLaw M).toMeasure :=
  (coldNativeCellTrace_identDistrib M m Q).integrable_iff.mpr (integrable_cutoffTraceDefect M m Q.scale)

/-- The integrated actual-cell trace is exactly the origin trace at that cell scale. -/
theorem coldNativeCellTrace_integral (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) :
    (∫ ω, coldNativeCellTrace M m Q ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ ω, cutoffTraceDefect M m Q.scale ω ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
  (coldNativeCellTrace_identDistrib M m Q).integral_eq

/-- Genuine trace subadditivity on the actual native partition, with no stochastic assumptions. -/
theorem coldNativeCellTrace_subadditive (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (r : ℕ) (ω : Cutoff.CutoffSample 2) :
    coldNativeCellTrace M m Q ω ≤ squareCellMean Q r (fun R => coldNativeCellTrace M m R.val ω) := by
  simp_rw [coldNativeCellTrace_eq_normalized]
  let F := coldNativePlateauFamily M m Q
  exact square_trace_subadditive Q (F.elliptic ω) (F.parent ω) (F.cells r ω)

/-- Genuine integrated trace subadditivity, using only the actual translated-cell laws. -/
theorem coldNativeCellTrace_mean_subadditive (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (r : ℕ) :
    (∫ ω, coldNativeCellTrace M m Q ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ∫ ω, cutoffTraceDefect M m (Q.scale-r) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  have h := integral_mono (coldNativeCellTrace_integrable M m Q)
    (integrable_squareCellMean Q r (fun R => coldNativeCellTrace_integrable M m R.val))
    (coldNativeCellTrace_subadditive M m Q r)
  rw [integral_squareCellMean Q r (fun R => coldNativeCellTrace_integrable M m R.val)] at h
  have he : (fun R : SquareCells Q r => ∫ ω, coldNativeCellTrace M m R.val ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      (fun _ => ∫ ω, cutoffTraceDefect M m (Q.scale-r) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) := by
    funext R
    rw [coldNativeCellTrace_integral,scale_eq_sub_of_mem_descendantsAtDepth R.property]
  rw [he,squareCellMean_const] at h
  exact h

/-- Actual lag means are nonincreasing at one literal coefficient and true fixed frame. -/
theorem coldNativeMean_antitone (M : ABKModel 2) (m : ℤ) : Antitone (coldNativeMean M m) := by
  apply antitone_nat_of_succ_le
  intro ell
  have h := coldNativeCellTrace_mean_subadditive M m (originCube 2 (m+((ell+1:ℕ):ℤ))) 1
  have he : (originCube 2 (m+((ell+1:ℕ):ℤ))).scale-(1:ℕ) = m+(ell:ℤ) := by
    simp only [originCube,Int.natCast_add,Int.natCast_one]
    ring
  simpa only [he,coldNativeMean,coldNativeTrace,coldNativeCellTrace,cutoffTraceDefect] using h

end ASDExplicitGamma.Cold
